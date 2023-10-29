import numpy.linalg as lin
import numpy as np
import json
import sys

if __name__ == "__main__":
    N = M = 0
    if len(sys.argv) == 2:
        N = int(sys.argv[1])
        M = N
    elif len(sys.argv) == 3:
        N = int(sys.argv[1])
        M = int(sys.argv[2])
    else:
        print(
            """Incorrect usage-
                For square N X N matrix: python3 input-creator N
                For rectangular N X M matrix: python3 input-creator N M"""
        )
        exit(1)

    MAX_ELEM = 10
    mat_ran = np.random.uniform(-MAX_ELEM, MAX_ELEM, size=(N, M))

    U, D, V = lin.svd(mat_ran)
    mat_ran = mat_ran.tolist()
    U = U.tolist()
    V = V.tolist()
    D = D.tolist()

    dict_svd = {"m": mat_ran, "u": U, "d": D, "v": V}

    json_file_path = "./data/matrix.in"

    with open(json_file_path, "w") as json_file:
        # Write the dictionary to the JSON file
        json.dump(dict_svd, json_file, indent=4)

    # change m to be wrong
    rand_i = np.random.randint(N)
    rand_j = np.random.randint(M)
    mat_ran[rand_i][rand_j] += 1e-3
    dict_svd = {"m": mat_ran, "u": U, "d": D, "v": V}

    json_file_path = "./data/matrix-wrong.in"

    with open(json_file_path, "w") as json_file:
        # Write the dictionary to the JSON file
        json.dump(dict_svd, json_file, indent=4)

    print(f"Python: Successfully created inputs for {N} X {M}!")
