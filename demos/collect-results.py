import shutil
import os

demos = ["counter", "twitter-clone", "message-groups", "rubis", "quoddy"]
dest = "results/temp/"

for demo in demos:
    path = demo + "/benchmark/measurements/" + demo + "/bench-results/"
    for op in ["weak", "op_mixed", "mixed", "strong", "weak_datacentric", "strong_datacentric",
               "datacentric_mixed_in_opcentric_impl"]:
        if op in ["weak_datacentric", "strong_datacentric"] and demo in ["counter", "message-groups"]:
            continue

        local_path = os.getcwd() + "/" + path + op
        if not os.path.isdir(local_path):
            continue

        src = local_path + "/" + sorted(os.listdir(local_path))[-1]
        dst = os.getcwd() + "/" + dest + demo + "/" + op + "/"

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
