## Aristotle key4 commands

Single file submit:

```bash
/root/workspace/benchmark/evaluation/aristotle/scripts/submit_formal_to_aristotle_key4.sh \
  /root/workspace/benchmark/JSON2LEAN/lean/problems/problem-1.lean
```

Single file submit and wait/download:

```bash
/root/workspace/benchmark/evaluation/aristotle/scripts/submit_formal_to_aristotle_key4.sh \
  /root/workspace/benchmark/JSON2LEAN/lean/problems/problem-1.lean \
  --wait \
  --destination /root/workspace/benchmark/JSON2LEAN/aristotle_problem_1_key4_result.tar.gz
```

Batch submit:

```bash
/root/workspace/benchmark/evaluation/aristotle/scripts/submit_batch_to_aristotle_key4.sh \
  /root/workspace/benchmark/JSON2LEAN/lean/problems/problem-{46..50}.lean
```

Batch submit with wait:

```bash
/root/workspace/benchmark/evaluation/aristotle/scripts/submit_batch_to_aristotle_key4.sh \
  /root/workspace/benchmark/JSON2LEAN/lean/problems/problem-{46..50}.lean \
  -- --wait
```
