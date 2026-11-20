"""Count consecutive critical-line zeros across the published height by FLINT's Turing check."""
import argparse
import ctypes as C
from pathlib import Path
import flint
from flint import acb, arb, ctx

H = 3000175332800
LAST_PUBLISHED = 12363153437138


def native_ordinates(count, precision):
    # Public 64-bit FLINT 3.6 arb_mat_struct and matrix-entry accessor.
    # Use FLINT itself to allocate balls, set the fmpz index and print enclosures.
    if C.sizeof(C.c_void_p)!=8 or flint.__FLINT_VERSION__!="3.6.0":
        raise RuntimeError("use --portable with this version or architecture")
    dirs = Path(flint.__file__).resolve().parent.parent/"python_flint.libs"
    libs = [p for p in dirs.glob("*flint*") if p.suffix==".dll" or ".so" in p.name]
    if len(libs)!=1:
        raise RuntimeError("use --portable when the wheel does not expose its FLINT library")
    lib = C.CDLL(str(libs[0]))
    word, ptr = C.c_int64, C.c_void_p

    class Matrix(C.Structure):
        _fields_ = [("entries",ptr),("rows",word),("cols",word),("stride",word)]

    def bind(name, result, *args):
        fn = getattr(lib,name)
        fn.restype, fn.argtypes = result,args
        return fn

    init = bind("arb_mat_init",None,C.POINTER(Matrix),word,word)
    clear = bind("arb_mat_clear",None,C.POINTER(Matrix))
    entry = bind("arb_mat_entry_ptr",ptr,C.POINTER(Matrix),word,word)
    index_set = bind("fmpz_init_set_si",None,C.POINTER(word),word)
    index_clear = bind("fmpz_clear",None,C.POINTER(word))
    batch = bind("acb_dirichlet_platt_hardy_z_zeros",word,ptr,C.POINTER(word),word,word)
    to_string = bind("arb_get_str",ptr,ptr,word,word)
    release = bind("flint_free",None,ptr)
    matrix, index = Matrix(), word()
    init(C.byref(matrix),1,count)
    index_set(C.byref(index),LAST_PUBLISHED)
    try:
        assert matrix.rows==1 and matrix.cols==count and matrix.stride>=count
        done = batch(entry(C.byref(matrix),0,0),C.byref(index),count,precision)
        if done!=count:
            raise ArithmeticError(f"FLINT isolated {done} of {count} requested zeros")
        result = []
        for i in range(count):
            string = to_string(entry(C.byref(matrix),0,i),28,0)
            try:
                result.append(arb(C.string_at(string).decode("ascii")))
            finally:
                release(string)
        return result
    finally:
        index_clear(C.byref(index))
        clear(C.byref(matrix))


def verify(count,portable):
    if not 2<=count<10**7:
        raise ValueError("expected a positive finite batch")
    ctx.prec = 96
    ctx.threads = 2
    if portable:
        zeros = acb.zeta_zeros(LAST_PUBLISHED,count)
        assert len(zeros)==count and all(z.real==arb(1)/2 for z in zeros)
        ys = [z.imag for z in zeros]
    else:
        ys = native_ordinates(count,ctx.prec)
    assert ys[0]<H<ys[1] and all(a<b for a,b in zip(ys,ys[1:]))
    high = ys[-1].floor().unique_fmpz()
    assert high is not None and H<high<ys[-1]
    print("starting index",LAST_PUBLISHED,"count",count,"first",ys[0].str(24),
          "last",ys[-1].str(24),"certified RH height",high,"extension",high-H,flush=True)


if __name__=="__main__":
    cli = argparse.ArgumentParser()
    cli.add_argument("--count",type=int,default=2048)
    cli.add_argument("--portable",action="store_true")
    args = cli.parse_args()
    verify(args.count,args.portable)
