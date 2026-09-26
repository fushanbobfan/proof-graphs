#!/usr/bin/env python3
"""A proposer backed by a step-level Lean tactic model served by llama.cpp.

BFS-Prover-V2 is a completion model, not a chat model: the prompt is a Lean tactic state followed by `:::`, and
the reply is one tactic. `propose` therefore calls `/v1/completions`, strips whatever of the prompt the model
echoed, and returns the first line of what follows. Sampling several completions at a temperature gives the
candidates an expansion needs; duplicates are dropped, order preserved.

  python scripts/step_prover.py --benchmark   # latency and candidates on three fixed states, no Lean

The model is served by `D:\\ucla\\agent-harness\\scripts\\start-llama-server.ps1 -Profile bfsprover`.
"""

from __future__ import annotations

import argparse
import concurrent.futures
import json
import re
import statistics
import time
import urllib.request
from typing import Any, Callable

from search_harness import State

ENDPOINT = "http://127.0.0.1:8080/v1/completions"
SEPARATOR = ":::"
MODEL_LOG: list[dict[str, Any]] | None = None  # prompts and replies, when a runner wants them
CONTROL = re.compile(r"[\x00-\x08\x0b-\x1f]")


# llama.cpp generates the `n` completions of one request one after another inside a single slot, so a request
# for n costs n times a single completion: measured on this server, 16 completions as two requests of n=8 took
# 43 s while the same 16 as concurrent single-completion requests took 1.5 s. `complete` therefore asks for one
# completion per request and issues them together. What is sampled is unchanged: `samples` independent
# completions of the same prompt at the same temperature.
MAX_CONCURRENT = 16


def one_completion(prompt: str, temperature: float, max_tokens: int, model: str,
                   timeout: float = 180.0) -> str | None:
    body = {"model": model, "prompt": prompt, "temperature": temperature, "max_tokens": max_tokens,
            "n": 1, "stop": ["\n\n"]}
    request = urllib.request.Request(ENDPOINT, data=json.dumps(body).encode("utf-8"),
                                     headers={"Content-Type": "application/json"})
    started = time.monotonic()
    try:
        with urllib.request.urlopen(request, timeout=timeout) as response:
            reply = json.loads(response.read().decode("utf-8"))
    except Exception as error:  # noqa: BLE001 - a server failure is recorded as no candidate
        if MODEL_LOG is not None:
            MODEL_LOG.append({"model": model, "prompt": prompt, "error": f"{type(error).__name__}: {error}"[:200],
                              "seconds": round(time.monotonic() - started, 2)})
        return None
    text = (reply.get("choices") or [{}])[0].get("text", "")
    if MODEL_LOG is not None:
        MODEL_LOG.append({"model": model, "prompt": prompt, "reply": text, "usage": reply.get("usage"),
                          "seconds": round(time.monotonic() - started, 2)})
    return text


def complete(prompt: str, samples: int, temperature: float, max_tokens: int, model: str,
             timeout: float = 180.0) -> list[str]:
    """The model's `samples` completions of one prompt, as concurrent single-completion requests."""
    with concurrent.futures.ThreadPoolExecutor(max_workers=min(samples, MAX_CONCURRENT)) as pool:
        futures = [pool.submit(one_completion, prompt, temperature, max_tokens, model, timeout)
                   for _ in range(samples)]
        return [text for text in (f.result() for f in futures) if text is not None]


def tactic_of(text: str, prompt: str = "") -> str | None:
    """The tactic in one completion: the first non-empty line after whatever of the prompt the model echoed,
    cleaned of code fences and control characters. llama.cpp returns the continuation alone unless asked to
    echo, but the model's own card describes it as echoing the state, so both are handled."""
    if prompt and text.startswith(prompt):
        text = text[len(prompt):]
    elif prompt and SEPARATOR in text[:len(prompt) + len(SEPARATOR)]:
        text = text.split(SEPARATOR, 1)[1]
    for line in text.split("\n"):
        line = CONTROL.sub("", line).strip().strip("`").strip()
        if line.startswith("by "):
            line = line[3:].strip()
        if line and not line.startswith("--"):
            return line
    return None


def candidates(goal: str, samples: int, temperature: float, max_tokens: int, model: str) -> list[str]:
    """Distinct tactics the model proposes for one goal, in the order returned."""
    prompt = goal.rstrip() + SEPARATOR
    out: list[str] = []
    for text in complete(prompt, samples, temperature, max_tokens, model):
        tactic = tactic_of(text, prompt)
        if tactic is not None and tactic not in out:
            out.append(tactic)
    return out


def proposer(samples: int, temperature: float, max_tokens: int, model: str,
             fallback: list[str] | None = None) -> Callable[[State], list[str]]:
    """A proposer that shows the model the first goal only, since it was trained on one tactic state, and
    appends `fallback` (a menu) after the model's candidates when one is given."""
    def propose(state: State) -> list[str]:
        out = candidates(state.goals[0], samples, temperature, max_tokens, model) if state.goals else []
        return out + [t for t in (fallback or []) if t not in out]
    return propose


def server_alive() -> bool:
    try:
        with urllib.request.urlopen("http://127.0.0.1:8080/v1/models", timeout=5) as response:
            return response.status == 200
    except Exception:  # noqa: BLE001
        return False


BENCHMARK_GOALS = [
    "⊢ ∀ (n : ℕ), n + 0 = n",
    "x y : ℝ\nh : x ≤ y\n⊢ x - y ≤ 0",
    "α : Type u_1\nl : List α\na : α\n⊢ (a :: l).length = l.length + 1",
]


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--benchmark", action="store_true")
    parser.add_argument("--samples", type=int, default=4)
    parser.add_argument("--temperature", type=float, default=0.8)
    parser.add_argument("--max-tokens", type=int, default=64)
    parser.add_argument("--model", default="bfsprover")
    parser.add_argument("--repeats", type=int, default=3)
    args = parser.parse_args()
    if not args.benchmark:
        parser.error("--benchmark is the only mode")
    if not server_alive():
        raise SystemExit("no model server on 127.0.0.1:8080")
    rows = []
    for goal in BENCHMARK_GOALS:
        for _ in range(args.repeats):
            started = time.monotonic()
            got = candidates(goal, args.samples, args.temperature, args.max_tokens, args.model)
            rows.append({"goal": goal.split("\n")[-1][:40], "seconds": round(time.monotonic() - started, 2),
                         "candidates": got})
    for row in rows:
        print(json.dumps(row, ensure_ascii=False))
    print(json.dumps({"medianSeconds": statistics.median(r["seconds"] for r in rows),
                      "medianCandidates": statistics.median(len(r["candidates"]) for r in rows)}))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
