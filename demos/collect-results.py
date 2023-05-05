import shutil
import os
import sys

working_dir = os.getcwd()
source = sys.argv[1] if sys.argv[1].startswith("/") else working_dir + "/" + sys.argv[1]
destination = sys.argv[2] if sys.argv[2].startswith("/") else working_dir + "/" + sys.argv[2]

print("Collecting from " + source + " into " + destination)

for configuration in os.listdir(source):
    config_source = source + "/" + configuration
    if not os.path.isdir(config_source):
        continue

    print("Found benchmark configuration: " + config_source)

    config_destination = destination + "/" + configuration + "/"

    timestamps = sorted(filter(lambda x: os.path.isdir(config_source + "/" + x), os.listdir(config_source)))
    if not timestamps:
        print("no timestamps found in: " + config_source)
        continue

    files_dir = config_source + "/" + timestamps[-1]
    files = list(filter(lambda x: not os.path.isdir(files_dir + "/" + x), os.listdir(files_dir)))
    if not files:
        print("source directory empty: " + files_dir)
        continue

    if len(files) != 8:  # TODO: combine directories if necessary
        print("files missing in: " + files_dir)
    else:
        if os.path.isdir(config_destination):
            shutil.rmtree(config_destination)
        shutil.copytree(files_dir, config_destination)

print("Done collecting results")
