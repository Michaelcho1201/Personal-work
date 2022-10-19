def decimal_right_shift(num):
    """
    Right shifts num by one digit

    :param num: (int) a positive intger
    :return: (int) num right shifted by one digit
    """
    right = int(num / 10)
    if right == 0:
        return True
    else:
        return False


def banana(num):
    apple = decimal_right_shift(num)
    if apple == True:
        print(apple)
    else:
        banana(num)


def main():
    x = int(input("enter any integer"))
    banana(x)
