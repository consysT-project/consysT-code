python3 process-results.py processed-triggers.csv \
../results/default/large-local-bench-results/webshop/mixed/:100 \
../results/default/large-local-bench-results/webshop/mixed_trigger/:100 \
../results/default/large-local-bench-results/webshop/op_mixed/:100 \
../results/default/large-local-bench-results/webshop/op_mixed_trigger/:100 \
../results/default/large-local-bench-results/trigger-chat/mixed/:100 \
../results/default/large-local-bench-results/trigger-chat/mixed_trigger/:100 \
../results/default/large-local-bench-results/trigger-chat/op_mixed/:100 \
../results/default/large-local-bench-results/trigger-chat/op_mixed_trigger/:100 \
../results/default/large-local-bench-results/trigger-document-share/mixed/:100 \
../results/default/large-local-bench-results/trigger-document-share/mixed_trigger/:100 \
../results/default/large-local-bench-results/trigger-document-share/op_mixed/:100 \
../results/default/large-local-bench-results/trigger-document-share/op_mixed_trigger/:100 \

python3 generate-graphs.py latency_processed-triggers.csv latency_normalized-triggers.csv \
../results/default/large-local-bench-results/webshop/mixed/:../results/default/large-local-bench-results/webshop/mixed_trigger/ \
../results/default/large-local-bench-results/webshop/op_mixed/:../results/default/large-local-bench-results/webshop/op_mixed_trigger/ \
../results/default/large-local-bench-results/trigger-chat/mixed/:../results/default/large-local-bench-results/trigger-chat/mixed_trigger/ \
../results/default/large-local-bench-results/trigger-chat/op_mixed/:../results/default/large-local-bench-results/trigger-chat/op_mixed_trigger/ \
../results/default/large-local-bench-results/trigger-document-share/mixed/:../results/default/large-local-bench-results/trigger-chat/mixed_trigger/ \
../results/default/large-local-bench-results/trigger-document-share/op_mixed/:../results/default/large-local-bench-results/trigger-chat/op_mixed_trigger/ \

python3 generate-graphs.py throughput_processed-triggers.csv throughput_normalized-triggers.csv \
../results/default/large-local-bench-results/webshop/mixed/:../results/default/large-local-bench-results/webshop/mixed_trigger/ \
../results/default/large-local-bench-results/webshop/op_mixed/:../results/default/large-local-bench-results/webshop/op_mixed_trigger/ \
../results/default/large-local-bench-results/trigger-chat/mixed/:../results/default/large-local-bench-results/trigger-chat/mixed_trigger/ \
../results/default/large-local-bench-results/trigger-chat/op_mixed/:../results/default/large-local-bench-results/trigger-chat/op_mixed_trigger/ \
../results/default/large-local-bench-results/trigger-document-share/mixed/:../results/default/large-local-bench-results/trigger-chat/mixed_trigger/ \
../results/default/large-local-bench-results/trigger-document-share/op_mixed/:../results/default/large-local-bench-results/trigger-chat/op_mixed_trigger/