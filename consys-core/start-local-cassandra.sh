#!/bin/bash

ccm create consys_test -v 4.0-beta4

ccm populate -n 3
ccm start
