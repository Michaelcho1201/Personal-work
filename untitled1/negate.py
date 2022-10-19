def negate(line):
    new_string = ""
    line_list = line.split()
    for digit in range(len(line_list)):
        integer = int(line_list[digit])
        new_integer = 255 - integer
        new_digit = str(new_integer)
        new_string = new_string + new_digit + " "
    print(new_string)
    return new_string


negate("1 2 3 10 50 30")
x = type(negate("1 2 3 4 5 6"))

print(x)
