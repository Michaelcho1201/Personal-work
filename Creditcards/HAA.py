def reverse(line):
    blank = ""
    reverse_list = line.split()
    reverse_list.reverse()
    for digit in range(len(reverse_list)):
        reverse_integer = int(reverse_list[digit])
        reverse_string = str(reverse_integer)
        blank = blank + reverse_string + " "
    final_reverse = blank.rstrip()
    print(final_reverse)


reverse("1 2 3 4 5 6")
