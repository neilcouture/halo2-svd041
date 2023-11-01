import numpy.linalg as lin
import numpy as np

if __name__ == "__main__":
    N = 1000
    MAX_ELEM = 10
    max_error = 0
    for _ in range(1000):
        mat = np.random.uniform(-MAX_ELEM, MAX_ELEM, size=(N, N))
        # Inf norm
        norm = np.linalg.norm(mat, ord=2)
        # rescale matrix so that ||mat||_inf \in (1,100)
        mat = mat / norm * np.random.uniform(1, 100)
        U, D, V = lin.svd(mat)
        mat_recon = U @ np.diag(D) @ V
        diff = mat - mat_recon
        # normalized error
        diff_norm = np.linalg.norm(diff, ord=2) / np.linalg.norm(mat, ord=2)
        if diff_norm > max_error:
            max_error = diff_norm

    print(f"Error = {max_error}")

# RESULTS:
# N = 100, max_error = 1.10 e-14
# N = 1000, max_error =1.14 e-14
