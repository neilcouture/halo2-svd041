import numpy.linalg as lin
import random
import itertools
import math
import numpy as np
import json

def ran_mat(n):
    mat = []
    for i in range(0,n):
        line = []
        for j in range(0,n):
            #r = random.randint(-1000, 1000)
            r = random.uniform(-10, 10)
            line = line + [r]
        mat = mat + [line]
    return mat

N=10
mat_ran = ran_mat(N)

U, D, V = lin.svd(mat_ran)
U = U.tolist()
V = V.tolist()
D = D.tolist()

dict_svd = {"m": mat_ran, "u": U, "d": D, "v": V}

json_file_path = "./data/matrix.in"

with open(json_file_path, 'w') as json_file:
    # Write the dictionary to the JSON file
    json.dump(dict_svd, json_file)
