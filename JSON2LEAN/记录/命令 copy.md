```bash
for f in /root/workspace/benchmark/JSON2LEAN/raw_results/*.tar.gz; do
  [ -e "$f" ] || continue
  base="$(basename "$f" .tar.gz)"
  out="/root/workspace/benchmark/JSON2LEAN/raw_results/$base"

  if [ -d "$out" ] && [ "$(find "$out" -mindepth 1 | head -n 1)" ]; then
    echo "skip already extracted: $out"
    continue
  fi

  mkdir -p "$out"
  echo "extracting $f -> $out"
  tar -xzf "$f" -C "$out"
done



export ARISTOTLE_API_KEY='arstl_dFx8pKCNXKWvI-wLg0bacdkJjl4p2YhYl2CmA_bkOlc'

mkdir -p /root/workspace/benchmark/JSON2LEAN/raw_results
mkdir -p /root/workspace/benchmark/JSON2LEAN/raw_results/status_json

while read -r name pid; do
  [ -n "$name" ] || continue

  echo
  echo "========== $name | $pid =========="

  status_file="/root/workspace/benchmark/JSON2LEAN/raw_results/status_json/${name}_${pid}.json"

  curl -s \
    -H "X-API-Key: $ARISTOTLE_API_KEY" \
    "https://aristotle.harmonic.fun/api/v2/project/$pid" \
    -o "$status_file"

  cat "$status_file" | jq '{
    project_id,
    status,
    percent_complete,
    created_at,
    last_updated_at,
    file_name,
    description,
    output_summary
  }'

  status="$(jq -r '.status' "$status_file")"

  if [ "$status" = "COMPLETE" ] || [ "$status" = "COMPLETE_WITH_ERRORS" ]; then
    out="/root/workspace/benchmark/JSON2LEAN/raw_results/${name}_${pid}.tar.gz"
    echo "downloading -> $out"
    curl -fL \
      -H "X-API-Key: $ARISTOTLE_API_KEY" \
      "https://aristotle.harmonic.fun/api/v2/project/$pid/result" \
      -o "$out" \
    && echo "saved: $out" \
    || echo "download failed: $name $pid"
  else
    echo "skip download, current status: $status"
  fi

  sleep 1
done <<'EOF'
problem_61 630fd910-6d9c-4c14-853e-d41bd5828d17
problem_62 c5cd921f-c5be-4517-8114-6e5f5405355c
problem_63 5c46c083-9806-4c21-87c2-5feaf3b3c933
problem_64 6cb9a018-83bd-4fff-b23f-6123de1f34e2
problem_65 b83132ce-c04f-4ab6-a1cf-bb29ea6d5d30
problem_86 525e3fc1-8f30-4759-80c3-e53a63793453
problem_87 7ca043d4-d478-4f4b-a942-db35fe9dc1be
problem_88 d4a7590f-887d-4e48-a6da-cd0ebe10c0e6
problem_89 2fed04c3-aac5-4033-9c6d-2c0ad25d5480
problem_101 e49b4f79-ed0d-4138-9062-debe6a7e5a55
problem_102 7bf901c6-b08d-4fa7-b3b0-f2d779d800b8
problem_103 78ac2098-a89d-43c6-8cf6-79132d323380
problem_104 092820f0-e420-493f-829e-fa53d053cd66
problem_105 0b979fa8-5288-492f-9d5b-99262b9fa8de
problem_128 8adea06d-d082-4e76-9c3f-7d0af7e4dc4d
problem_129 944d0c20-10e7-44ca-aed6-2c48b6aa9b3e
problem_130 23295142-9d44-47e4-ab25-ae84e33e58f2
problem_131 81e537ed-22a5-414e-b32b-c4c967fa4497
problem_132 baa2d6a0-37e9-481c-8574-3b00b7712bd1
problem_139 a9686fa7-97b0-4236-8fef-75d281d952a9
problem_140 625abd39-71f7-4ff7-bada-a551d17d5c36
problem_141 3d844fc1-81f4-4538-9e36-1f322338b1a2
problem_142 af499f05-b10a-4bf8-a7d5-7329cf29160a
problem_155 3115070a-8ec5-4b71-a0e7-d86b069c4a62
problem_159 2c28b4bd-c6ef-4425-abe9-2586ea785375
problem_163 8e4ea5dd-0d42-4c8d-a234-00a9f322b4ea
problem_176 57f8375b-e5c7-4674-8398-8964a53ae385
problem_180 17ba7ec4-3f10-4651-8226-6fe4afaabdc7
problem_200 38df661d-5e58-4bb7-9e98-de50b709ebf8
problem_187 16c7bc03-551f-4e9a-9e41-6702fcf8af7b
problem_188 abdc021a-be55-4e87-9e20-1956ede8fd13
problem_194 4a1f9f48-2e2b-4515-8b88-b9cd93679619
problem_197 426c6140-7afa-4670-85c0-5eb3114c4f44

EOF


```


```bash
export ARISTOTLE_API_KEY='arstl_wycmg-ivo4UZpJnuLHKzEboPelYvuXMdCF2cq5vxlRM'

mkdir -p /root/workspace/benchmark/JSON2LEAN/raw_results
mkdir -p /root/workspace/benchmark/JSON2LEAN/raw_results/status_json

while read -r name pid; do
  [ -n "$name" ] || continue

  echo
  echo "========== $name | $pid =========="

  status_file="/root/workspace/benchmark/JSON2LEAN/raw_results/status_json/${name}_${pid}.json"

  curl -s \
    -H "X-API-Key: $ARISTOTLE_API_KEY" \
    "https://aristotle.harmonic.fun/api/v2/project/$pid" \
    -o "$status_file"

  cat "$status_file" | jq '{
    project_id,
    status,
    percent_complete,
    created_at,
    last_updated_at,
    file_name,
    description,
    output_summary
  }'

  status="$(jq -r '.status' "$status_file")"

  if [ "$status" = "COMPLETE" ] || [ "$status" = "COMPLETE_WITH_ERRORS" ]; then
    out="/root/workspace/benchmark/JSON2LEAN/raw_results/${name}_${pid}.tar.gz"
    echo "downloading -> $out"
    curl -fL \
      -H "X-API-Key: $ARISTOTLE_API_KEY" \
      "https://aristotle.harmonic.fun/api/v2/project/$pid/result" \
      -o "$out" \
    && echo "saved: $out" \
    || echo "download failed: $name $pid"
  else
    echo "skip download, current status: $status"
  fi

  sleep 1
done <<'EOF'
problem_41 cbf42be9-6589-4990-8001-f888a8dbc886
problem_42 228c50ab-c57e-465b-8a68-6344f259475e
problem_43 19daa6e4-5d1d-4e57-b43a-faab51d97ba3
problem_44 cde7b0ce-7527-4b7d-bc67-22eec86f4433
problem_45 7b474fa4-0aa2-4a11-8666-548154740bdf
problem_55 d05799cb-cf83-44f5-b9c0-2c089a97f6db
problem_56 a1a76e1e-c9a7-4ee9-9caf-31a01d31d602
problem_57 e17a10f1-4fc1-4e20-bcdc-ed41d28e8227
problem_58 c90e1a26-eafe-4beb-9e04-37cb6285fb3a
problem_59 d299000c-9f96-4843-92a9-d1ba703abcc7
problem_60 a20e6d81-027f-492b-b080-0ad66bab9774
problem_81 f661c611-57c7-43d7-bfa2-1e4341be4100
problem_82 037f71e1-4991-4d51-98d8-f1d226a67e10
problem_83 22463fb9-3bec-4acb-8fd5-b3c41748b1d0
problem_84 4706c886-7915-49e9-85ca-7f6d04e38da2
problem_85 3804c734-1e0d-470e-88b2-3c19ff236455
problem_106 01c1d192-b4c1-4aba-ac0e-f4e07b0af2a9
problem_107 a59ae4f4-a8d3-4484-a5a6-d41ee2282ed7
problem_108 fc45ce87-ad9d-4f0e-9c81-62352423eb1e
problem_109 12a962b2-8eec-48fb-9acf-6c28dc55820f
problem_110 619ae772-2033-49f1-ad03-3a45fc4f03e1
problem_122 bd1a995f-6bea-4f24-9352-17a191c350a6
problem_123 b4071fd3-ee3d-41f6-b541-c8c7088d49a6
problem_124 6eed7a42-0a10-4b39-aead-ce9bf88595a0
problem_125 47d6c370-f1bc-46ca-9ef7-27cb90359fe7
problem_126 03395a91-5913-47dc-8d7f-21d212a9850e
problem_127 1dbcc0d4-46ef-46ad-9de9-73533bca5651
problem_143 64681cca-1c96-455e-a343-0717d42dd312
problem_144 381335c5-6dd5-4e99-82cb-6b210bf666e1
problem_145 b08f7979-239c-44af-b6da-a87b4bbec8f5
problem_146 e73f3565-8333-4a91-9b06-73c08e29b86b
problem_162 19ac1637-6c9a-4fee-bc13-2efb3ffed087
problem_168 d5afb3bd-7a47-40ed-88f7-8c920e24fa51
problem_169 51988df4-c2dc-4023-8627-05a8ad844508
problem_170 ae89ead2-383b-490a-b671-2d01e6368364
problem_173 f8a98c87-ff8c-42a9-9ad5-1f479fa93027
problem_177 c57ce78f-d0c9-4c8c-b079-dd7008844016
problem_178 64e57a35-0b7a-432b-99b2-d3371bb9a378
problem_181 b290947c-7797-4a90-81f2-43adcc35fd3c
problem_182 81df54d0-b208-4e36-9d51-c004b433c24e
problem_183 b153a58d-cd28-4c12-a01b-a80f301b6b1e
problem_184 6118f66a-12f7-49cc-a75c-d188bd2d7ef8
problem_189 d1bb90a9-568e-4d5f-b848-052731213601
problem_192 0cb7f384-8570-4455-b5cf-dd9f3e33d368
problem_193 b14ea050-51c7-4133-ab13-fb5386abcae9

EOF


```











```bash cy
/root/workspace/benchmark/evaluation/aristotle/scripts/submit_formal_to_aristotle.sh \
  /root/workspace/benchmark/JSON2LEAN/lean/problems/problem-200.lean

/root/workspace/benchmark/evaluation/aristotle/scripts/submit_batch_to_aristotle.sh \
  /root/workspace/benchmark/JSON2LEAN/lean/problems/problem-{128..135}.lean

ARISTOTLE_API_KEY="arstl_dFx8pKCNXKWvI-wLg0bacdkJjl4p2YhYl2CmA_bkOlc" \
/root/workspace/benchmark/evaluation/aristotle/.venv/bin/python \
/root/workspace/benchmark/evaluation/aristotle/scripts/aristotle_request.py status \
78324917-068a-436e-a6d9-240c01b84945

ARISTOTLE_API_KEY="arstl_dFx8pKCNXKWvI-wLg0bacdkJjl4p2YhYl2CmA_bkOlc" \
/root/workspace/benchmark/evaluation/aristotle/.venv/bin/python \
/root/workspace/benchmark/evaluation/aristotle/scripts/aristotle_request.py download \
78324917-068a-436e-a6d9-240c01b84945 \
--destination /root/workspace/benchmark/JSON2LEAN/aristotle_problem_22_result.tar.gz

```

```bash yf

/root/workspace/benchmark/evaluation/aristotle/scripts/submit_formal_to_aristotle_newkey.sh \
  /root/workspace/benchmark/JSON2LEAN/lean/problems/problem-194.lean

root@iZ6we1uiu32uwf1iblvjxfZ:~# /root/workspace/benchmark/evaluation/aristotle/scripts/submit_formal_to_aristotle_newkey.sh \
  /root/workspace/benchmark/JSON2LEAN/lean/problems/problem-70.lean
{
  "project_id": "d30fccc3-413a-4112-8e72-4a405942f86c",
  "status": "QUEUED",
  "percent_complete": null,
  "created_at": "2026-05-01T10:04:00.958012",
  "last_updated_at": "2026-05-01T10:04:01.246359",
  "file_name": "lean.tar.gz",
  "description": "Prove all theorems with sorry in problems/probl...",
  "output_summary": null
}

root@iZ6we1uiu32uwf1iblvjxfZ:~# /root/workspace/benchmark/evaluation/aristotle/scripts/submit_formal_to_aristotle_newkey.sh \
  /root/workspace/benchmark/JSON2LEAN/lean/problems/problem-100.lean
{
  "project_id": "4857022c-9517-42cd-95c8-3c3284bb4617",
  "status": "QUEUED",
  "percent_complete": null,
  "created_at": "2026-05-01T10:30:39.611053",
  "last_updated_at": "2026-05-01T10:30:39.898885",
  "file_name": "lean.tar.gz",
  "description": "Prove all theorems with sorry in problems/probl...",
  "output_summary": null
}

root@iZ6we1uiu32uwf1iblvjxfZ:~# /root/workspace/benchmark/evaluation/aristotle/scripts/submit_formal_to_aristotle_newkey.sh \
  /root/workspace/benchmark/JSON2LEAN/lean/problems/problem-161.lean
{
  "project_id": "ed4b1a41-9ee5-4feb-8eaf-b4fa654c542e",
  "status": "QUEUED",
  "percent_complete": null,
  "created_at": "2026-05-01T11:04:09.805156",
  "last_updated_at": "2026-05-01T11:04:10.030237",
  "file_name": "lean.tar.gz",
  "description": "Prove all theorems with sorry in problems/probl...",
  "output_summary": null
}

root@iZ6we1uiu32uwf1iblvjxfZ:~# /root/workspace/benchmark/evaluation/aristotle/scripts/submit_formal_to_aristotle_newkey.sh \
  /root/workspace/benchmark/JSON2LEAN/lean/problems/problem-168.lean
{
  "project_id": "33ad7f36-d74c-42a4-ae7b-35470804474a",
  "status": "QUEUED",
  "percent_complete": null,
  "created_at": "2026-05-01T11:09:41.220561",
  "last_updated_at": "2026-05-01T11:09:41.451699",
  "file_name": "lean.tar.gz",
  "description": "Prove all theorems with sorry in problems/probl...",
  "output_summary": null
}

{
  "project_id": "e646d3e3-cd8d-4225-a516-c997c68699ad",
  "status": "QUEUED",
  "percent_complete": null,
  "created_at": "2026-05-01T16:14:16.720316",
  "last_updated_at": "2026-05-01T16:14:17.032880",
  "file_name": "lean.tar.gz",
  "description": "Prove all theorems with sorry in problems/probl...",
  "output_summary": null
}


/root/workspace/benchmark/evaluation/aristotle/scripts/submit_batch_to_aristotle_newkey.sh \
  /root/workspace/benchmark/JSON2LEAN/lean/problems/problem-{133..140}.lean



ARISTOTLE_API_KEY="arstl_2cbFqXoaNCKLxYzR7DyZogbboJAriSY4haQAhL_d1HY" \
/root/workspace/benchmark/evaluation/aristotle/.venv/bin/python \
/root/workspace/benchmark/evaluation/aristotle/scripts/aristotle_request.py status \
3b012c1f-d874-4224-b9f7-f8cd1c8db454



ARISTOTLE_API_KEY="arstl_2cbFqXoaNCKLxYzR7DyZogbboJAriSY4haQAhL_d1HY" \
/root/workspace/benchmark/evaluation/aristotle/.venv/bin/python \
/root/workspace/benchmark/evaluation/aristotle/scripts/aristotle_request.py download \
5f35f418-69ae-4647-9c55-ec57c4862c74 \
--destination /root/workspace/benchmark/JSON2LEAN/aristotle_problem_199_result.tar.gz

```

```bash
/root/workspace/benchmark/evaluation/aristotle/scripts/submit_batch_to_aristotle_newkey.sh \
  /root/workspace/benchmark/JSON2LEAN/lean/problems/problem-{3..10}.lean

不等待批量跑
```

```bash
mkdir -p /root/workspace/benchmark/JSON2LEAN/aristotle_problem_40_result

tar -xzf /root/workspace/benchmark/JSON2LEAN/aristotle_problem_40_result.tar.gz \
  -C /root/workspace/benchmark/JSON2LEAN/aristotle_problem_40_result
``


```bash
/root/workspace/benchmark/evaluation/aristotle/scripts/submit_batch_to_aristotle.sh \
  /root/workspace/benchmark/JSON2LEAN/lean/problems/problem-{3..5}.lean
‵‵`


```bash  wt
/root/workspace/benchmark/evaluation/aristotle/scripts/submit_formal_to_aristotle_key3.sh \
  /root/workspace/benchmark/JSON2LEAN/lean/problems/problem-200.lean


/root/workspace/benchmark/evaluation/aristotle/scripts/submit_batch_to_aristotle_key3.sh \
  /root/workspace/benchmark/JSON2LEAN/lean/problems/problem-{125..130}.lean

ARISTOTLE_API_KEY="arstl_wycmg-ivo4UZpJnuLHKzEboPelYvuXMdCF2cq5vxlRM" \
/root/workspace/benchmark/evaluation/aristotle/.venv/bin/python \
/root/workspace/benchmark/evaluation/aristotle/scripts/aristotle_request.py status \
0eb482ce-86ba-47ab-8cc5-087b531728b4

ARISTOTLE_API_KEY="arstl_wycmg-ivo4UZpJnuLHKzEboPelYvuXMdCF2cq5vxlRM" \
/root/workspace/benchmark/evaluation/aristotle/.venv/bin/python \
/root/workspace/benchmark/evaluation/aristotle/scripts/aristotle_request.py download \
7f17e3be-e4a8-445e-bff7-4140bbec102f \
--destination /root/workspace/benchmark/JSON2LEAN/aristotle_problem_30_result.tar.gz
```

```bash 停下
ARISTOTLE_API_KEY="对应提交时用的 key" \
/root/workspace/benchmark/evaluation/aristotle/.venv/bin/python \
/root/workspace/benchmark/evaluation/aristotle/scripts/aristotle_request.py cancel \
PROJECT_ID
```

```bash 其他
/root/workspace/benchmark/evaluation/aristotle/scripts/submit_formal_to_aristotle_key4.sh \
  /root/workspace/benchmark/JSON2LEAN/lean/problems/problem-200.lean


/root/workspace/benchmark/evaluation/aristotle/scripts/submit_batch_to_aristotle_key4.sh \
  /root/workspace/benchmark/JSON2LEAN/lean/problems/problem-{116..126}.lean


ARISTOTLE_API_KEY="arstl_6UKK7ngECW7IbkCKWHyoNghlNzUYgGINDtIa5tDPI8o" \
/root/workspace/benchmark/evaluation/aristotle/.venv/bin/python \
/root/workspace/benchmark/evaluation/aristotle/scripts/aristotle_request.py status \
f8dcf31a-39da-4259-8234-f839ee2b9c55


ARISTOTLE_API_KEY="arstl_6UKK7ngECW7IbkCKWHyoNghlNzUYgGINDtIa5tDPI8o" \
/root/workspace/benchmark/evaluation/aristotle/.venv/bin/python \
/root/workspace/benchmark/evaluation/aristotle/scripts/aristotle_request.py download \
69eb2c06-5655-47e0-9096-918a434490e9 \
--destination /root/workspace/benchmark/JSON2LEAN/aristotle_problem_118_result.tar.gz
```
