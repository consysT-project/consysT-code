import csv
import sys
import argparse
import os
import plotly.graph_objects as go
import plotly.express as px
import pandas as pd
import numpy as np, scipy.stats as st



arg_parser = argparse.ArgumentParser(description='Process benchmark outputs.')
arg_parser.add_argument('output', metavar='Output',
help='Name of the output file.')
arg_parser.add_argument('inputs', metavar='Inputs', nargs='*',
help='Directories that contains only csv files that are parsed. Every directory is assumed to be a different data point.' +
'Every direction has to have a transaction number associated to it. Example: results/benchmark1/:100')


args = arg_parser.parse_args()


# creates a list of lists with all the paths for a single project


data = pd.DataFrame([], columns = ['file', 'mean', 'median' ,'len', 'std', 'conf_1_low', 'conf_1_high', 'conf_2_low', 'conf_2_high'])
print("Start processing...", end = '')
for input in args.inputs :
	splitted_input = input.split(":", 1)
	path = splitted_input[0]
	num_of_transactions = int(splitted_input[1])
	csv_paths = [path + '/' + filepath for filepath in os.listdir(path)]
	times = []
	for csv_path in csv_paths:
		print(f"\rProcessing {csv_path}...", end ='')
		csv_read = csv.reader(open(csv_path), delimiter=',')
		headers = next(csv_read, None)

		for row in csv_read:
			times.append(int(row[1]))

	times_ms = [(time / 1000000) / num_of_transactions for time in times]

	#Compute interesting data points
	arr = np.array(times_ms)

	count = len(arr)
	mean = np.mean(arr)
	median = np.median(arr)
	standard_dev = np.std(arr)
	confidence_1sig = st.t.interval(0.6827, count - 1, loc=mean, scale=st.sem(arr))

	confidence_2sig = st.t.interval(0.9545, count - 1, loc=mean, scale=st.sem(arr))

	print()
	print("***")
	print(f'Results for {path}')
	print(f'Total number of entries: {count}')
	print(f'Mean: {mean}ms')
	print(f'Median: {median}ms')
	print(f'Standard deviation: {standard_dev}ms')
	print(f'68% confidence interval: {confidence_1sig}')
	print(f'95% confidence interval: {confidence_2sig}')

	# Add data that should be plotted
	new_data = pd.DataFrame(
		[[path, mean, median, count, standard_dev, confidence_1sig[0], confidence_1sig[1], confidence_2sig[0], confidence_2sig[1]]],
		columns = ['file', 'mean', 'median' ,'len', 'std', 'conf_1_low', 'conf_1_high', 'conf_2_low', 'conf_2_high']
	)
	data = data.append(new_data)

print("***")
data.set_index('file')
print(data)

data.to_csv(args.output, sep = ';')

# fig = px.bar(data, x = 'file', y = 'mean')
# fig.show()
