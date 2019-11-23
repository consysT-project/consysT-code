#!/bin/bash

python3 process-results.py processed-contention.csv results/contention/mgrp-cont-mixed-1/:1000 results/contention/mgrp-cont-strong-1/:1000 results/contention/mgrp-cont-mixed-10/:1000 results/contention/mgrp-cont-strong-10/:1000 results/contention/mgrp-cont-mixed-100/:1000 results/contention/mgrp-cont-strong-100/:1000 results/contention/mgrp-cont-mixed-1000/:1000 results/contention/mgrp-cont-strong-1000/:1000

python3 generate-graphs.py processed-contention.csv normalized-contention.csv results/contention/mgrp-cont-mixed-1/:results/contention/mgrp-cont-strong-1/ results/contention/mgrp-cont-mixed-10/:results/contention/mgrp-cont-strong-10/ results/contention/mgrp-cont-mixed-100/:results/contention/mgrp-cont-strong-100/ results/contention/mgrp-cont-mixed-1000/:results/contention/mgrp-cont-strong-1000/
