"""Parameter-independent floors on the displayed local bound in rStation 168."""
from flint import arb, ctx


def run():
    ctx.prec = 192
    height = arb(3000175332800)
    for sigma, fraction, target, floor in [
        (".80", ".008", 75000, 248640),
        (".81", ".05", 230000, 342880),
        (".82", ".05", 19000, 209823),
    ]:
        length = arb(fraction)*height+1280000
        b = 2*arb(sigma)-1
        bound = length*(6/length)**b * arb(1).exp()*(length/6).log()/(2*arb.pi()*(1+b))
        assert 0 < b and b < 1 and length > 6 and bound > floor > target
        print(sigma, fraction, bound.str(18), target)


if __name__ == "__main__":
    run()
