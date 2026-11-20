"""Arb bounds for the discrete Hilbert transform on periodic residue classes."""

from math import gcd

from flint import acb, arb, ctx


def positive_schur_pivots(matrix):
    """Certify Hermitian positive definiteness by its successive Schur complements."""
    dimension = len(matrix)
    for k in range(dimension):
        pivot = matrix[k][k].real
        if not pivot > 0:
            raise ArithmeticError(f"Schur pivot {k} has no positive lower bound")
        for i in range(k + 1, dimension):
            factor = matrix[i][k] / pivot
            for j in range(k + 1, i):
                matrix[i][j] -= factor * matrix[j][k].conjugate()
            matrix[i][i] = acb(matrix[i][i].real - abs(matrix[i][k])**2 / pivot)


def certify_residues(modulus, residues, target):
    """Prove ||H|| < target on the stated residues modulo modulus."""
    residues = sorted(set(residues))
    if modulus < 1 or not residues or not all(0 <= r < modulus for r in residues):
        raise ValueError("expected a nonempty subset of residues")
    pi = arb.pi()
    bound = arb(target)
    spectral_bound = modulus * bound / pi - 1
    matrix = []
    for i, r in enumerate(residues):
        row = [acb(0, -1 / (pi * (r-s) / modulus).sin()) for s in residues[:i]]
        matrix.append(row + [acb(spectral_bound)])
    positive_schur_pivots(matrix)
    return bound


def integer_hilbert(modulus):
    """Upper bound K for convolution by 1/(n-m) on units modulo modulus."""
    pi = arb.pi()
    if modulus in (1, 2):
        return pi / modulus
    if modulus == 6:
        return pi * (1 + 2 / arb(3).sqrt()) / 6
    targets = {30: ".984447", 210: ".915503"}
    if modulus not in targets:
        raise ValueError("supply an upper bound via certify_residues for this modulus")
    return certify_residues(modulus, (r for r in range(modulus) if gcd(r, modulus) == 1),
                            targets[modulus])


def logarithmic_error(w):
    """Schur error after passing from 1/(n-m) to local log frequencies."""
    w = arb(w)
    if not w > 0:
        raise ValueError("window width must be positive")
    return (w/2).exp() * w.expm1()**2 / 12


def hilbert_coefficient(modulus, w, padding):
    """Coefficient of sum n|a_n|^2 in the one-sided weighted mean square."""
    w, padding = arb(w), arb(padding)
    mass = 1 - 4 / (arb.pi() * w * padding)
    if not mass > 0:
        raise ValueError("convolution window needs positive certified mass")
    return (integer_hilbert(modulus) + logarithmic_error(w)) / mass


if __name__ == "__main__":
    ctx.prec = 384
    for modulus in (2, 6, 30, 210):
        print(modulus, integer_hilbert(modulus).str(18),
              hilbert_coefficient(modulus, ".001", 10**9).str(18))
