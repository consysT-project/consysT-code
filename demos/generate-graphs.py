import csv
import sys
import argparse
import os
#import plotly.graph_objects as go
#import plotly.express as px
import pandas as pd
import numpy as np, scipy.stats as st



arg_parser = argparse.ArgumentParser(description='Generate graphs from processed results.')
arg_parser.add_argument('input', metavar='File', help='Name of the file with the processed results.')
arg_parser.add_argument('output', metavar='File', help='Name of the output file.')
arg_parser.add_argument('comparisons', metavar='Comparisons', nargs='*', help='The a list of pairs of names of benchmarks (file) to compare. Example: results/benchmark1/:results/benchmark2/')


args = arg_parser.parse_args()


# creates a list of lists with all the paths for a single project


input = pd.read_csv(args.input, sep=';', index_col = 'file',
converters = {'mean': float, 'median': float, 'std': float, 'len': int, 'index' : int, 'conf_1_low': float, 'conf_1_high': float, 'conf_2_low': float, 'conf_2_high': float})
print(input)

data = pd.DataFrame([], columns = ['file', 'normalized_mean', 'normalized_conf_1_low', 'normalized_conf_1_high', 'normalized_conf_2_low', 'normalized_conf_2_high'])

for comparison in args.comparisons :
	splitted_comparison = comparison.split(":", 1)
	value_file = splitted_comparison[0]
	baseline_file = splitted_comparison[1]

	absolute_mean = input.at[value_file, 'mean']
	normalized_mean = absolute_mean / input.at[baseline_file, 'mean']
	normalized_conf_1sig_low = (input.at[value_file, 'conf_1_low'] * normalized_mean) / absolute_mean
	normalized_conf_1sig_high = (input.at[value_file, 'conf_1_high'] * normalized_mean) / absolute_mean
	normalized_conf_2sig_low = (input.at[value_file, 'conf_2_low'] * normalized_mean) / absolute_mean
	normalized_conf_2sig_high = (input.at[value_file, 'conf_2_high'] * normalized_mean) / absolute_mean



	new_data = pd.DataFrame(
		[[value_file, normalized_mean, normalized_conf_1sig_low, normalized_conf_1sig_high, normalized_conf_2sig_low, normalized_conf_2sig_high]],
		columns = ['file', 'normalized_mean', 'normalized_conf_1_low', 'normalized_conf_1_high', 'normalized_conf_2_low', 'normalized_conf_2_high']
	)
	data = data.append(new_data)

print("***")
print(data)

data.to_csv(args.output, sep = ';')

#px.bar(input, y = 'mean').show()
#px.bar(data, x = 'file', y = 'normalized_mean').show()






# print("Start processing...", end = '')
# for input in args.inputs :
# 	splitted_input = input.split(":", 1)
# 	path = splitted_input[0]
# 	num_of_transactions = int(splitted_input[1])
# 	csv_paths = [path + '/' + filepath for filepath in os.listdir(path)]
# 	times = []
# 	for csv_path in csv_paths:
# 		print(f"\rProcessing {csv_path}...", end ='')
# 		csv_read = csv.reader(open(csv_path), delimiter=',')
# 		headers = next(csv_read, None)
#
# 		for row in csv_read:
# 			times.append(int(row[1]))
#
# 	times_ms = [(time / 1000000) / num_of_transactions for time in times]
#
# 	#Compute interesting data points
# 	arr = np.array(times_ms)
#
# 	count = len(arr)
# 	mean = np.mean(arr)
# 	median = np.median(arr)
# 	standard_dev = np.std(arr)
# 	confidence_interval_1sigma = st.t.interval(0.6827, count - 1, loc=mean, scale=st.sem(arr))
# 	confidence_interval_2sigma = st.t.interval(0.9545, count - 1, loc=mean, scale=st.sem(arr))
#
# 	print()
# 	print("***")
# 	print(f'Results for {path}')
# 	print(f'Total number of entries: {count}')
# 	print(f'Mean: {mean}ms')
# 	print(f'Median: {median}ms')
# 	print(f'Standard deviation: {standard_dev}ms')
# 	print(f'68% confidence interval: {confidence_interval_1sigma}')
# 	print(f'95% confidence interval: {confidence_interval_2sigma}')
#
# 	# Add data that should be plotted
# 	new_data = pd.DataFrame([[path, mean, count, standard_dev, confidence_interval_1sigma, confidence_interval_2sigma]], columns = ['file', 'mean', 'len', 'std', 'conf_1', 'conf_2'])
# 	data = data.append(new_data)
#
# print("***")
# print(data)
#
# data.to_csv('results.csv', sep = ';', index_label = 'index')
#
# fig = px.bar(data, x = 'file', y = 'mean')
# fig.show()
