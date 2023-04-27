import shutil
import os
import sys

working_dir = os.getcwd()
source = working_dir + "/" + sys.argv[1]
destination = working_dir + "/" + sys.argv[2]

for configuration in os.listdir(source):
    local_path = working_dir + "/" + configuration
    if not os.path.isdir(local_path):
        continue

    src = local_path + "/" + sorted(os.listdir(local_path))[-1]
    dst = destination + "/" + configuration + "/"

    if not os.path.isdir(src):
        print("source directory does not exist: " + src)
    else:
        files = os.listdir(src)
        if not files:
            print("source directory empty: " + src)
        else:
            if len(files) != 8:  # TODO: combine directories if necessary
                print("files missing in: " + src)
            else:
                if os.path.isdir(dst):
                    shutil.rmtree(dst)
                shutil.copytree(src, dst)

print("done")
