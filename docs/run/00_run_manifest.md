# Zeta 85 research run

- Started: 2026-08-10 15:38 PDT
- Hard stop: 2026-08-11 00:00 PDT
- Target: prove `liminf N0simple(T)/N(T) >= 0.85`.
- Accepted infrastructure: all results and inputs in `zeta-two-thirds.pdf` and its transcript explanation.
- Review constraint: at most one narrow review/integration checkpoint per 90-minute cycle.
- Drive folder: https://drive.google.com/drive/folders/1HXvqKcsh8oOJ6OEMHd477hXgEvugUlum

## Cycle 1 routes

1. Certificate architecture: derive the weakest exact input sufficient for 85%.
2. Arithmetic construction: extend the usable prime-side information beyond bandwidth one or replace it with a restricted estimate.
3. Hybrid construction: force non-overlap between the 0.6725 certificate and complementary unconditional information.

## Coordinator calculation

For the Montgomery-Taylor optimal window at general support `lambda`,

`c*(lambda) = sqrt(2) tan(lambda/sqrt(2)) / (1 + (lambda/sqrt(2)) tan(lambda/sqrt(2)))`

and the rank-trace simple-on-line certificate is `2 - 1/c*(lambda)`. Reaching exactly 0.85 through this direct route requires

`lambda >= 1.473426925085247`.

Thus a restricted prime-side theorem sufficient for the Montgomery-Taylor kernel through effective support 1.47343 is one explicit completion route. This is a construction target, not an assumption.
