# Strict-Isolated-8h 时间曲线数据说明

生成日期：2026-05-05

## 文件

- 每题时间明细：`strict_isolated_8h_per_problem_times_20260505.csv`
- 1h 粒度精确曲线数据：`strict_isolated_8h_hourly_curve_20260505.csv`
- SVG 图：`strict_isolated_8h_success_curve_20260505.svg`
- PDF 图：`strict_isolated_8h_success_curve_20260505.pdf`
- 生成脚本：`plot_strict_isolated_8h_curve.py`

## 主标准

按 `推荐统计标准_20260505.md`：8 小时以内、原题、无 `exact?/sorry/sorryAx/admit`、Aristotle 去 `yes -xiu`、m2f 去跨题 import，且 m2f 不因 `history_log_sum` 扣正确性。

## 主结果

- M2F：143/200 = 71.50%
- Aristotle：125/200 = 62.50%

## 1h 粒度精确数据

| 时间预算 | M2F 解出 | M2F 正确率 | Aristotle 解出 | Aristotle 正确率 |
|---:|---:|---:|---:|---:|
| 0h | 0 | 0.00% | 0 | 0.00% |
| 1h | 119 | 59.50% | 72 | 36.00% |
| 2h | 134 | 67.00% | 99 | 49.50% |
| 3h | 141 | 70.50% | 110 | 55.00% |
| 4h | 142 | 71.00% | 116 | 58.00% |
| 5h | 142 | 71.00% | 119 | 59.50% |
| 6h | 142 | 71.00% | 120 | 60.00% |
| 7h | 143 | 71.50% | 123 | 61.50% |
| 8h | 143 | 71.50% | 125 | 62.50% |

## 绘图说明

图使用 `log(1+x)` 伪 log 横坐标和平滑曲线连接 1h 粒度精确观测点，因此 0h 点保留在图中。M2F 使用绿色实线，Aristotle 使用橙色虚线，轴名为 `Time budget (hours, log(1+x) scale)` 和 `Cumulative success rate (%)`。

建议 caption：

\\caption{Cumulative strict success rate of M2F and Aristotle under increasing time budgets. M2F solves 143/200 targets within 8 hours, while Aristotle solves 125/200.}

## m2f 过滤说明

8h 内 `done` 为 147 题；主标准去掉 4 个跨题 import 后为 143 题。

跨题 import 被去掉的题：

11, 79, 109, 118

`history_log_sum` 保留在主榜中的题：

1, 4, 5, 13, 16, 40, 41, 47, 50, 51, 52, 76, 127, 128, 129, 130, 160, 164, 166, 167, 195, 196
