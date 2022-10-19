def fun_name(a_param):
    x = a_param * 2
    print(x)


fun_name(3)


def add(a, b, c):
    s = a + b + c
    print(s)


print(add(3, 4, 5))


def even(y):
    if y % 2 == 0:
        return True
    else:
        return False


print(even(5))


def force(mass, accleeration):
    calc = mass * accleeration
    return calc


print(force(5, 2))
