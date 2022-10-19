"""
    CS051P Lab Assignments: PPM Processing

    Name: Michael Cho

    Date:   4/10/2020

    The goal of this assignment is to give you practice working with nested lists
    by writing a program that manipulates the entire image with multiple lines.
"""


def process(lines, rows, cols):
    """
    Takes lines of a ppm image and returns a new list of length rows, with rows number of nested lists that have cols
    times 3  amount of integers between 0 and 255.
    :param lines: (str) any multi lined string representing the body of a image
    :param rows: (int) a positive integer that cam be multiplied by cols to equal the number of pixels in the image.
    :param cols: (int) a positive integer that cam be multiplied by rows to equal the number of pixels in the image.
    :return: (list) a new list with rows amount of nested lists that have 3 times cols amount of integers
    between 0 and 255.
    """

    # Sets variables main_list and new_list to blank lists.
    main_list = []
    new_list = []
    # uses for loop to turn and add each line into main_list.
    for line in lines:
        main_list += line.split()
    spot = 0
    num_sub_lists = 0

    # Uses while not loop to produce smaller lists with a length of cols*3  until the number of lists equals rows.
    while not num_sub_lists == rows:
        new_sub_list = main_list[spot: cols * 3 + spot]

        # Turns each digit into an integer.
        for index in range(len(new_sub_list)):
            new_int = int(new_sub_list[index])
            new_sub_list[index] = new_int

        # Appends each nested list into  new_list.
        new_list.append(new_sub_list)
        num_sub_lists = num_sub_lists + 1
        spot = spot + (cols * 3)

    # Returns new_list.
    return new_list


def read_ppm(filename):
    """
   Takes the string of a ppm file and returns the result of running the process function on the body with the rows and
   cols file as the ppm image.
   :param filename: (str) Any ppm file.
   :return: (list) a list of list of integers produced by the process function using the body of the ppm fle.
    """

    # Opens the fil and starts reading the header, setting size to the second line of the header.
    file_in = open(filename, "r")
    file_in.readline()
    size = file_in.readline()
    file_in.readline()

    # Sets rows equal to the second number and cols equal to the first number.
    rows = int(size[2])
    cols = int(size[0])

    # Returns the result of the function process on the ppm file body with rows and cols.
    return process(file_in.readlines(), rows, cols)


def write_ppm(image, filename):
    """
    Takes a list of list of integers and a new ppm file. It turns the list into a string and writes its as an image
    file.
    :param image: (list) a list of list of integers between 0 and 255.
    :param filename:(str) a ppm file.
    """

    # Sets variable num lists to zero.
    num_lists = 0

    # Opens the new file and writes the ppm header.
    with open(filename, "w") as image_out:
        image_out.write("P3" + "\n")
        rows = str(len(image))
        cols = str(int(len(image[0]) / 3))
        image_out.write(cols + " ")
        image_out.write(rows + "\n")
        image_out.write("255" + "\n")

        # Turns each list into a string and adds it to empty string called empty_line and writes it.
        for main_index in range(len(image)):
            empty_line = ""
            for index in range(len(image[num_lists])):
                new_digit = str(image[num_lists][index])
                empty_line = empty_line + new_digit + " "
            image_out.write(empty_line + "\n")
            num_lists = num_lists + 1


def scale(image, row_scale, col_scale):
    """
    Takes a list of list of integers and keeps only every row_scale-th row of the main list and then keeps only every
    col_scale-th column of the remaining nested lists. It then adds the nested list to a new list and returns the new
    list.
    :param image: (int) a list of list of integers between 0 and 255.
    :param row_scale: (int) a positive integer.
    :param col_scale: (int) another positive integer.
    :return: a new list of lists of the remaining integers.
    """
    # Sets variable new_scale_list and total_new_lst to blank list
    new_scale_list = []
    total_new_list = []

    # Creates sub_lists out of the nested lists in the the row_scale-th position and appends them to new_scale_list.
    for index in range(len(image)):
        if int((index + row_scale) % row_scale) == 0:
            sub_list = image[index]
            new_scale_list.append(sub_list)

    # Creates new nested lists called total_sub_lists with remaining integers and appends them to total_new_list.
    for new_index in range(len(new_scale_list)):
        total_sub_list = []
        new_sub_list = new_scale_list[new_index]
        if col_scale >= 2:
            for sub_index in range(len(new_sub_list)):
                if int((sub_index + (col_scale * 3)) % (col_scale * 3)) == 0 and sub_index + 2 <= len(new_sub_list):
                    total_sub_list += new_sub_list[sub_index: sub_index + 3]
        else:
            total_sub_list += new_sub_list
        total_new_list.append(total_sub_list)

    # Returns total_new_list.
    return total_new_list


def main():
    # TODO:
    """
    This function will first ask for an input file name and an output  file name. It then asks for a positive integer
    height scaling factor and a positive integer width scaling factor.  If user does not input a positive integer for
    either of these, it will ask again until user does so. It then sets the height and width scaling factors as
    row_scale and col_scale. It then uses function read_ppm to read and process the input file into a list of lists of
    integers between 0 and 255. It then takes the list of list of integers and scales it using the function scale as
    well as row_scale and col_scale. It then takes the scaled list of list of integers and uses write_ppm to write it on
    the output file.
    """
    # Asks the user for an input and output file  name and runs function read_ppm on it, setting the result to read_list
    in_filename = (input("Enter any filename."))
    out_filename = (input("Enter any out_filename."))
    read_list = read_ppm(in_filename)

    # Asks for two positive integers for row_scale and col_scale, repeating it if the conditions are not met.
    row_scale = int(input("Enter any positive integer."))
    while not row_scale > 0:
        print("That is not a positive integer.")
        row_scale = int(input("Enter any positive integer."))
    col_scale = int(input("Enter another positive integer."))
    while not col_scale > 0:
        print("That is not a positive integer.")
        col_scale = int(input("Enter another positive integer."))

    # Runs function scale on read_list, row_scale, and col_scale, setting the result equal to new_list.
    new_list = scale(read_list, row_scale, col_scale)

    # Uses write_ppm to write the new list on the output file.
    write_ppm(new_list, out_filename)


if __name__ == '__main__':
    main()
