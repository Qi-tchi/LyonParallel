from fractions import Fraction
from math import gcd
from functools import reduce

def proportional_natural_numbers(l1):
    """
    Takes a list of fractions and returns a list of natural numbers
    such that the ratios between the numbers correspond to the ratios
    between the original fractions.
    """
    def lcm(a, b):
        return a * b // gcd(a, b)
    
    def compute_lcm(numbers):
        return reduce(lcm, numbers)
    
    denominators = [frac.denominator for frac in l1]
    numerators = [frac.numerator for frac in l1]
    common_lcm = compute_lcm(denominators)
    
    l2 = [n * (common_lcm // d) for n, d in zip(numerators, denominators)]
    return l2

# Example usage:
# fractions_list =[Fraction(  13,6000000), 
#                   Fraction(1, 36000000), 
#                   Fraction(1,  3000000), 
#                   Fraction( 1, 3600000),
#                 Fraction(1,   36000000),
#                 Fraction(1,   36000000),
#                   Fraction(41,36000000)
#                   ]
# natural_numbers_list = proportional_natural_numbers(fractions_list)  


import re,sys

originalWeights = sys.argv[2] == "True"
with open(f"tmp/{sys.argv[3]}.out") as file:
    text = file.read()
match = re.search(rf"root-obj", text)
if match == None:
    root_value = False
else:
    root_value = True
with open(f"tmp/{sys.argv[3]}.interp", "w") as file:   

    # Regular expression pattern to capture the number after "s" and before "->"
    pattern = r"x_(\d+)_E(\d+)_(\d+)_([a-zA-Z0-1]+) \(\) Bool\n\s+(true|false)"

    # Perform the match
    matches = re.findall(pattern, text)
    output = []
    # print(matches)
    # with open(f"tmpParallel/tmp/{sys.argv[1]}.interp", "w") as file:
    for id,s,t,l,exist in matches:
        if sys.argv[1] == "float":
            if exist == "true":
                # write value of x
                if originalWeights:
                    file.write(f"y_{s}--{l}->{t} : ")
                c1 = (f"y_{s}--{l}->{t} ")
                ypattern = rf"y_(\d+)_E{s}_{t}_{l} \(\) (Int|Real)\n\s+\(/ ([-+]?\d*\.\d+) ([-+]?\d*\.\d+)\)" 
                # print(f"label {l} \n")
                match = re.search(ypattern, text)
                # print(match.groups())
                if match == None:
                    try:
                        ypattern = rf"y_(\d+)_E{s}_{t}_{l} \(\) (Int|Real)\n\s+([-+]?\d*\.\d+)"
                        match1 = re.search(ypattern, text)
                        file.write(f"{match1.groups()[2]}\n")
                        c2 = int(float(match1.groups()[2]))
                        c3 = 1
                        output.append((c1,c2,c3))
                    except AttributeError:
                        ypattern = rf"y_(\d+)_E{s}_{t}_{l}"
                        match1 = re.search(ypattern, text)
                        file.write(f"y_{match1.groups()[0]}\n")
                        print(f"y_{match1.groups()[0]} {s}--{l}->{t}: root-obj value, see .out file")
                else:
                    # if originalWeights:
                    #     file.write(f"{match.groups()[2]}/{match.groups()[3]} \n") 
                    c2 = int(float(match.groups()[2]))
                    c3 = int(float(match.groups()[3]))
                    if originalWeights:
                        file.write(f"{match.groups()[2]}/{match.groups()[3]} \n")
                    output.append((c1,c2,c3))
        else:
            if exist == "true":
                ypattern = rf"y_(\d+)_E{s}_{t}_{l} \(\) Int\n\s+(\d+)"
                match = re.search(ypattern, text)
                # print(match)
                if originalWeights:
                    file.write(f"y_s{s}->t{t}_{l} : {match.groups()[1]}\n")
                output.append((f"y_s{s}->t{t}_{l} ",int(match.groups()[1]),1))
    if not root_value :
        # normalizarion
        file.write("\n")
        fractions_list =[Fraction(c2,c3) for (c1,c2,c3) in output]
        natural_numbers_list = proportional_natural_numbers(fractions_list)
        for ((c1,c2,c3), x) in zip(output,natural_numbers_list):
            file.write(f"{c1}: {x}\n")
            
    file.write("\nrules eliminated?:\n")
    pattern = r"z_(\d+)_rl_(\d+) \(\) Bool\n\s+(true|false)"
    # Perform the match of eliminated rules
    matches = re.findall(pattern, text)
    for match in matches:
        file.write(f"rule {match[1]}: {match[2]}\n")

