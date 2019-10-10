from itertools import chain, combinations
import math
from scipy.stats import truncnorm
import matplotlib.pyplot as plt
import re
import random
import string
import os
import sys


USERS_COUNT = 1000
PRODUCTS_COUNT = 1000

LOGIN_REQUESTS = 500
REGISTER_REQUESTS = 500
SEARCH_REQUESTS = 500
ADD_CART_REQUESTS = 500
CHECK_CART_REQUESTS = 500
VIEW_INFO_REQUESTS = 500
ADD_BALANCE_REQUESTS = 500

HOST_COUNT = 1

"""
-h for help
-nh for setting host number 
-uc for setting user count
-pc for setting product count
"""

if len(sys.argv) > 0:
    if "-h" in sys.argv:
        print(
            "-h for help \n-nh for setting host number \n-uc for setting user count"
            + "\n-pc for setting product count"
        )
        sys.exit()
    for x in range(len(sys.argv)):
        if sys.argv[x] == "-nh":
            HOST_COUNT = int(sys.argv[x + 1])
            print("Set host count to:" + str(HOST_COUNT))
        if sys.argv[x] == "-uc":
            USERS_COUNT = int(sys.argv[x + 1])
            print("Set user count to:" + str(USERS_COUNT))
        if sys.argv[x] == "-pc":
            PRODUCTS_COUNT = int(sys.argv[x + 1])
            print("Set product count to:" + str(PRODUCTS_COUNT))

list_of_searches = []
script_dir = os.path.dirname(os.path.abspath(__file__))
dest_dir = os.path.join(script_dir, "gen_requests")

try:
    os.makedirs(dest_dir)
except OSError:
    pass  # already exists

# Helping functions
def get_search_with_atleast(num):
    viable_searches = [
        y[0] for y in list(filter(lambda x: x[1] >= num, list_of_searches))
    ]
    return viable_searches


def check_one_request(req, name):
    if req % HOST_COUNT != 0:
        print("The number of " + name + " is not cleanly divisible by HOST_COUNT")
        print(
            "Reduce it by {0} or increase it by {1}".format(
                str(req % HOST_COUNT), str(HOST_COUNT - (req % HOST_COUNT))
            )
        )
        return True
    return False


def check_host_requests():
    stop = False
    stop = check_one_request(LOGIN_REQUESTS, "LOGIN_REQUESTS") or stop
    stop = check_one_request(REGISTER_REQUESTS, "REGISTER_REQUESTS") or stop
    stop = check_one_request(SEARCH_REQUESTS, "SEARCH_REQUESTS") or stop
    stop = check_one_request(ADD_CART_REQUESTS, "ADD_CART_REQUESTS") or stop
    stop = check_one_request(CHECK_CART_REQUESTS, "CHECK_CART_REQUESTS") or stop
    stop = check_one_request(VIEW_INFO_REQUESTS, "VIEW_INFO_REQUESTS") or stop
    stop = check_one_request(ADD_BALANCE_REQUESTS, "ADD_BALANCE_REQUESTS") or stop
    if stop:
        exit()


def find_exponent(len, cnt):
    "Solves Len^x > cnt"
    x = 0
    while True:
        if len ** x > cnt:
            return x
        else:
            x += 1


def modified_powerset(iterable, cnt):
    "powerset([1,2,3],5) --> (1,) (2,) (3,) (1,2) (1,3)"
    "Only generates the part of the powerset that is needed."
    s = list(iterable)
    exp = find_exponent(len(s), cnt)
    end = exp + 1 if (len(s) + 1 > exp) else len(s) + 1
    pws = list(chain.from_iterable(combinations(s, r) for r in range(1, end)))
    return pws[:cnt]


def get_truncated_normal(mean=0, sd=1, low=0, upp=10):
    return truncnorm((low - mean) / sd, (upp - mean) / sd, loc=mean, scale=sd)


# Generation functions
def gen_users():
    users = []
    for x in range(USERS_COUNT):
        users.append(
            "User"
            + str(x)
            + "-"
            + "".join(random.choice(string.ascii_uppercase) for _ in range(10))
            + ";"
            + "".join(
                random.choice(string.digits + string.ascii_letters) for _ in range(10)
            )
        )
    return users


def gen_registrations():
    regist = []
    for x in range(REGISTER_REQUESTS):
        regist.append(
            "User"
            + str(x + USERS_COUNT)
            + "-"
            + "".join(random.choice(string.ascii_uppercase) for _ in range(10))
            + ";"
            + "".join(
                random.choice(string.digits + string.ascii_letters) for _ in range(10)
            )
        )
    return regist


def gen_searchWords():
    allowed = "1234567890qwertzuiopasdfghjklyxcvbnm"
    # No uppercase letters, since search function sets everything to lowercase anyway.
    sep = "_"
    combos = modified_powerset(allowed, SEARCH_REQUESTS)
    ret = list(map(lambda x: sep + "".join(x) + sep, combos))
    return ret


def gen_products(searchQueries):
    all_searches = [re.sub("_", "", x) for x in searchQueries]
    sep = "_"
    products = [sep] * PRODUCTS_COUNT

    mean_percentage = 0.375
    sd_percentage = 0.15
    vmean = int(round(mean_percentage * PRODUCTS_COUNT))
    vsd = int(round(sd_percentage * PRODUCTS_COUNT))
    vlow = 0
    vupp = PRODUCTS_COUNT
    X = get_truncated_normal(mean=vmean, sd=vsd, low=vlow, upp=vupp)
    """Get the samples from the normal distribution that indicate how many 
    items are returned for a query."""
    samples = [int(round(x)) for x in list(X.rvs(SEARCH_REQUESTS))]
    samples.sort(reverse=True)

    test = samples[0]

    for sample in samples:
        "Add the searchterm and sample size to the list of searches"
        list_of_searches.append(("_" + all_searches[0] + "_", sample))
        "Attach the search term to sample amount of products"
        prod1 = products[:sample]
        prod2 = products[sample:]
        products = prod2 + [x + all_searches[0] + "_" for x in prod1]
        all_searches = all_searches[1:]
    "Ensure that each product is unique (by numbering them :^)"
    for x in range(len(products)):
        products[x] = "UNIQUEPRODUCT" + str(x) + products[x]
    "Uncomment to check that function works"
    # print(len(products) == len(set(products)))
    # print(len(products) == PRODUCTS_COUNT)
    # print(len([x for x in products if "_1_" in x]) == test)
    "Uncomment to get an illustration of the normal distribution"
    # plt.hist(X.rvs(1000000,50), 99, facecolor='g', alpha=0.75,label="Number of requests per number of returned items")
    # plt.legend()
    # plt.show()
    return products


def gen_add_cart_requests(users):
    """
    Each request will be encoded as: 
    username;password;SearchWord;SizeOfReturned;NumberOfElements

    This is to be used as follows:
    Login with username and password

    The benchmark inputs the searchterm, adds the first NumberOfElements to the cart 
    and then adds the (NumberOfElements+1)th elements while measuring.
    Then cart is cleared, logged out and the same thing done again.
    """
    # Generate an amount of items in the cart inversely proportional to the amount of requests
    # Can be approximated with a normal distribution N(-5, 10) between 0 and 25
    elems_in_cart = []
    X = get_truncated_normal(mean=-5, sd=10, low=0, upp=25)
    samples = [int(round(x)) for x in list(X.rvs(ADD_CART_REQUESTS))]
    samples.sort()

    for sample in samples:
        searches = list(filter(lambda x: x[1] > sample, list_of_searches))
        chosenSearch = random.choice(searches)
        usr = random.choice(users)
        elems_in_cart.append(
            usr + ";" + chosenSearch[0] + ";" + str(chosenSearch[1]) + ";" + str(sample)
        )

    "Uncomment to get an illustration of the normal distribution"
    # plt.hist(X.rvs(1000000,50), 99, facecolor='g', alpha=0.75,label="Number of requests per number of items in cart")
    # plt.legend()
    # plt.show()
    return elems_in_cart


def gen_check_cart_requests(users):
    """
    Each request will be encoded as:
    username;password;SearchWord;SizeOfReturned;NumberOfElements

    This is to be used as follows: The benchmark inputs the searchterm, adds the
    NumberOfElements to the cart and then adds the required cash
    (NumberOfElements * 100) to the user. Then check out the cart. Then cart is
    cleared and the same thing done again.
    """
    # Generate an amount of items in the cart inversely proportional to the amount of requests
    # Can be approximated with a normal distribution N(-4, 10) between 1 and 26
    elems_in_cart = []
    X = get_truncated_normal(mean=-4, sd=10, low=1, upp=26)
    samples = [int(round(x)) for x in list(X.rvs(CHECK_CART_REQUESTS))]
    samples.sort()

    for sample in samples:
        searches = list(filter(lambda x: x[1] >= sample, list_of_searches))
        chosenSearch = random.choice(searches)
        usr = random.choice(users)
        elems_in_cart.append(
            usr + ";" + chosenSearch[0] + ";" + str(chosenSearch[1]) + ";" + str(sample)
        )

    "Uncomment to get an illustration of the normal distribution"
    # plt.hist(X.rvs(1000000,50), 99, facecolor='g', alpha=0.75,label="Number of requests per number of items in cart")
    # plt.legend()
    # plt.show()
    return elems_in_cart


def gen_view_info_requests():
    """
    Each request will be encoded as: 

    SearchWord;ElementToView

    This is to be used as follows: The benchmark inputs the searchterm, and
    views the elementToView. Note that this will be in the range 1 to the number
    of elements returned.
    """
    view_reqs = []
    searches = list(filter(lambda x: x[1] > 0, list_of_searches))

    for x in range(VIEW_INFO_REQUESTS):
        chosenSearch = random.choice(searches)
        view = random.choice(range(chosenSearch[1])) + 1
        assert view <= chosenSearch[1]
        view_reqs.append(chosenSearch[0] + ";" + str(view))

    return view_reqs


def gen_add_balance_requests(users):
    """
    Each request will be encoded as: 
    username;password;Money

    This is to be used as follows: The benchmark logs in, measures the time it
    takes to add balance, and logs out.
    """
    add_balance_reqs = []
    for x in range(VIEW_INFO_REQUESTS):
        usr = random.choice(users)
        add_balance_reqs.append(usr + ";" + str(random.choice(range(50, 500))))

    return add_balance_reqs


# Functions for adding everything into text files
# USERS AND PRODUCTS
def write_users_file(users):
    f = open(os.path.join(dest_dir, "users.txt"), "w")
    for u in users[:-1]:
        f.write(u + "\n")
    f.write(users[-1:][0])
    f.close()


def write_products_file(prods):
    f = open(os.path.join(dest_dir, "products.txt"), "w")
    for p in prods[:-1]:
        f.write(p + ";100" + "\n")
    f.write(prods[-1:][0] + ";100")
    f.close()


# WRITE FILE FUNCTION
def write_file(reqs, name):
    chunk_size = len(reqs) / HOST_COUNT
    chunks = [
        reqs[x : x + int(chunk_size)] for x in range(0, len(reqs), int(chunk_size))
    ]
    for x in range(len(chunks)):
        f = open(os.path.join(dest_dir, name + "_host_" + str(x) + ".txt"), "w")
        scrambled = sorted(chunks[x], key=lambda x: random.random())
        for u in scrambled[:-1]:
            f.write(u + "\n")
        f.write(scrambled[-1:][0])
        f.close()


# SEARCHWORDS:
check_host_requests()

search_wrds = gen_searchWords()

all_products = gen_products(search_wrds)
all_users = gen_users()

reg_reqs = gen_registrations()

add_cart_reqs = gen_add_cart_requests(all_users)
check_cart_reqs = gen_check_cart_requests(all_users)
view_reqs = gen_view_info_requests()
add_balance_reqs = gen_add_balance_requests(all_users)


write_products_file(all_products)
write_users_file(all_users)

write_file(all_users[:LOGIN_REQUESTS], "login_requests")
write_file(reg_reqs, "register_requests")
write_file(search_wrds, "search_requests")
write_file(add_cart_reqs, "add_cart_requests")
write_file(check_cart_reqs, "checkout_cart_requests")
write_file(view_reqs, "view_info_requests")
write_file(add_balance_reqs, "add_balance_requests")
