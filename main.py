import sys
import subprocess
import os


def isin(arr, func):
    for f in arr:
        if f == func:
            return True
    return False


def main():
    example = ""
    for line in sys.stdin:
        if len(line) == 1:
            break
        example += line

    example = example[:len(example) - 1]

    examplee = '''f(h(z)) -> f(x)
f(x) -> h(x)
h(g(x, y)) -> q(q(q(x)))'''
    examplee = "f(g(x)) -> g(f(x))"

    message = '''(set-logic QF_NIA)
'''

    rule = example.count("\n") + 1
    inqs = []
    inq = ""
    parts = []
    funcs = []
    variables = []
    amounts = []
    coefcounter = 0
    coefs = []
    smtinqs = []
    monotonous = []

    # находим список переменных
    for i in range(len(example) - 1):
        if example[i + 1] == '(' and not isin(funcs, example[i]):
            funcs.append(example[i])
        elif example[i] != ')' and (example[i - 1] == '(' or example[i + 1] == ')') and not isin(variables, example[i]) and not isin(funcs, example[i]):
            variables.append(example[i])

    # разбиваем сообщение на пары выражений
    for s in example:
        if s == '\n':
            inqs.append(inq)
            inq = ""
            continue
        inq += s
    inqs.append(inq)

    for s in inqs:
        parts.append(s.split(" -> "))

    scheme = []

    # перевод на язык скима
    for t in parts:
        for f in t:
            for i in range(len(f)):
                if f[i] == ',':
                    f = f[:i] + f[i + 1:]
                if isin(funcs, f[i]) and f[i + 1] == '(':
                    f = f[:i] + '(' + f[i] + ' ' + f[i + 2:]
            scheme.append(f.replace("  ", " "))

    # подсчёт количества переменных, принимаемых каждой функцией и создание списка коэффициентов
    for f in funcs:
        left = 0
        right = 0
        foundf = False
        founda = False
        amount = 0
        for s in scheme:
            if founda:
                break
            for i in s:
                if i == f:
                    foundf = True
                if foundf:
                    if left == right and i == ' ':
                        amount += 1
                    if i == '(':
                        left += 1
                    if i == ')':
                        right += 1
                    if right - left == 1:
                        founda = True
                        break
        amount += 1
        amounts.append(amount)
        coeff = []
        for i in range(amount):
            coeff.append("a" + str(coefcounter))
            coefcounter += 1
        coefs.append(coeff)

    # объявление переменных для z3
    for i in coefs:
        for j in i:
            message += "(declare-fun " + j + " () Int)\n"

    print("Функции и их коэффициенты (последний свободный):")
    for i in range(len(funcs)):
        print(funcs[i], coefs[i])

    print("\nПеременные:")
    print(variables)

    # неравенства из правил для z3
    for s in scheme:
        ready = False
        while not ready:
            for j in range(len(funcs)):
                for i in range(len(s)):
                    if i < len(s) and s[i] == funcs[j]:
                        s = s[:i] + coefs[j][len(coefs[j]) - 1] + ' + ' + s[i + 1 + len(funcs[j]):]
                        i += 3 + len(coefs[j][len(coefs[j]) - 1])
                        varamount = 0
                        left = 0
                        right = 0
                        part = ""
                        while i < len(s) and varamount != len(coefs[j]) - 1:
                            part += s[i]
                            if s[i] == '(':
                                left += 1
                            if s[i] == ')':
                                right += 1
                                if left != 0 and left == right:
                                    varamount += 1
                                    if varamount == len(coefs[j]) - 1:
                                        s = s[:i - len(part) + 1] + part + "*" + coefs[j][varamount - 1] + s[i+1:]
                                        i += len(part) - 5 + len(coefs[j][varamount - 1])
                                    else:
                                        s = s[:i - len(part) + 1] + part + "*" + coefs[j][varamount - 1] + " + " + s[i+1:]
                                        i += len(part) - 4 + len(coefs[j][varamount - 1])  # -1
                                    part = ""
                                    left = 0
                                    right = 0
                            if i < len(s) and left == right and isin(variables, s[i]):
                                varamount += 1
                                if varamount != len(coefs[j]) - 1:
                                    s = s[:i] + s[i] + "*" + coefs[j][varamount - 1] + " +" + s[i + 1:]
                                else:
                                    s = s[:i] + s[i] + "*" + coefs[j][varamount - 1] + s[i + 1:]
                                i += 1 + len(coefs[j][varamount - 1])
                            i += 1
            ready = True
            for f in funcs:
                for i in s:
                    if i == f:
                        ready = False
                        break
        smtinqs.append(s)

    for i in range(len(smtinqs)):
        if smtinqs[i][0] == '(' and smtinqs[i][len(smtinqs[i])-1] == ')':
            smtinqs[i] = smtinqs[i][1:len(smtinqs[i])-1]

    normal_ineqs = []

    # неравенства на человеческом языке для приведения подобных
    for s in smtinqs:
        while isin(s, '('):
            for i in range(len(s)):
                summands = []
                part = ""
                if i < len(s) and s[i] == '(':
                    start = i
                    i += 1
                    while s[i] != ')':
                        if s[i] == '(':
                            break
                        if s[i] == ' ':
                            if part != "":
                                summands.append(part)
                            part = ""
                            i += 1
                            continue
                        if s[i] != '+':
                            part += s[i]
                        i += 1
                    if part != "":
                        summands.append(part)
                        i += 1
                        end = i
                        i += 1
                        multi = ""
                        while i < len(s) and s[i] != ' ' and s[i] != ')':
                            multi += s[i]
                            i += 1
                        end += len(multi) + 1
                        result = ""
                        for k in range(len(summands) - 1):
                            result += summands[k] + "*" + multi + " + "
                        result += summands[len(summands) - 1] + "*" + multi
                        s = s[:start] + result[:len(result)] + s[end:]
                        #i = start + len(result) + len(s) - end
        normal_ineqs.append(s)

    message += "\n"

    # считаем множители при каждой переменной для каждой пары
    for i in range(0, len(normal_ineqs), 2):
        for v in variables:
            multipliers1 = []
            multipliers2 = []
            for j in range(len(normal_ineqs[i])):
                multiplier = []
                temp = ""
                if normal_ineqs[i][j] == v:
                    j += 2
                    while j < len(normal_ineqs[i]) and normal_ineqs[i][j] != ' ':
                        if normal_ineqs[i][j] == '*':
                            multiplier.append(temp)
                            temp = ""
                            j += 1
                            continue
                        temp += normal_ineqs[i][j]
                        j += 1
                    if temp != "":
                        multiplier.append(temp)
                if multiplier:
                    multipliers1.append(multiplier)
            i += 1
            for j in range(len(normal_ineqs[i])):
                multiplier = []
                temp = ""
                if normal_ineqs[i][j] == v:
                    j += 2
                    while j < len(normal_ineqs[i]) and normal_ineqs[i][j] != ' ':
                        if normal_ineqs[i][j] == '*':
                            multiplier.append(temp)
                            temp = ""
                            j += 1
                            continue
                        temp += normal_ineqs[i][j]
                        j += 1
                    if temp != "":
                        multiplier.append(temp)
                if multiplier:
                    multipliers2.append(multiplier)
            i -= 1

            if len(multipliers1) == 0 and len(multipliers2) == 0:
                continue

            message += "(assert (>= "

            if len(multipliers1) == 0:
                message += "0"
            if len(multipliers1) > 1:
                message += "(+ "
            for k in range(len(multipliers1)):
                if len(multipliers1[k]) > 1:
                    message += "(* "
                for q in range(len(multipliers1[k]) - 1):
                    message += multipliers1[k][q] + " "
                message += multipliers1[k][len(multipliers1[k]) - 1]
                if len(multipliers1[k]) > 1:
                    message += ")"
                if k != len(multipliers1) - 1:
                    message += " "
            if len(multipliers1) > 1:
                message += ")"
            message += " "

            if len(multipliers2) == 0:
                message += "0"
            if len(multipliers2) > 1:
                message += "(+ "
            for k in range(len(multipliers2)):
                if len(multipliers2[k]) > 1:
                    message += "(* "
                for q in range(len(multipliers2[k]) - 1):
                    message += multipliers2[k][q] + " "
                message += multipliers2[k][len(multipliers2[k]) - 1]
                if len(multipliers2[k]) > 1:
                    message += ")"
                if k != len(multipliers2) - 1:
                    message += " "
            if len(multipliers2) > 1:
                message += ")"
            message += "))\n"
        message += "\n"

    third = []
    test = message.split("\n\n")
    for i in range(1, len(test), 1):
        if test[i] != "":
            third.append(test[i].split("\n"))

    # считаем свободные члены для каждой пары
    for i in range(0, len(normal_ineqs), 2):
        frees1 = []
        frees2 = []
        frees = []
        free = ""
        for j in range(len(normal_ineqs[i])):
            if isin(variables, normal_ineqs[i][j]):
                break
            if normal_ineqs[i][j] == '+':
                continue
            if normal_ineqs[i][j] != ' ':
                free += normal_ineqs[i][j]
            if normal_ineqs[i][j] == ' ' and free != "":
                frees1.append([free])
                free = ""
                continue
            if normal_ineqs[i][j] == '*':
                frees.append(free[:len(free) - 1])
                free = ""
                j += 1
                while j < len(normal_ineqs[i]) and not isin(funcs, normal_ineqs[i][j]) and normal_ineqs[i][j] != ' ':
                    if normal_ineqs[i][j] == '*':
                        frees.append(free)
                        free = ""
                        j += 1
                        continue
                    free += normal_ineqs[i][j]
                    j += 1
                if free != "":
                    frees.append(free)
                if frees:
                    frees1.append(frees)
                break

        i += 1
        free = ""
        frees = []

        for j in range(len(normal_ineqs[i])):
            if isin(variables, normal_ineqs[i][j]):
                break
            if normal_ineqs[i][j] == '+':
                continue
            if normal_ineqs[i][j] != ' ':
                free += normal_ineqs[i][j]
            if normal_ineqs[i][j] == ' ' and free != "":
                frees2.append([free])
                free = ""
                continue
            if normal_ineqs[i][j] == '*':
                frees.append(free[:len(free) - 1])
                free = ""
                j += 1
                while j < len(normal_ineqs[i]) and not isin(funcs, normal_ineqs[i][j]) and normal_ineqs[i][j] != ' ':
                    if normal_ineqs[i][j] == '*':
                        frees.append(free)
                        free = ""
                        j += 1
                        continue
                    free += normal_ineqs[i][j]
                    j += 1
                if free != "":
                    frees.append(free)
                if frees:
                    frees2.append(frees)
                break

        message += "(assert (>= "
        if len(frees1) > 1:
            message += "(+ "
        for k in range(len(frees1)):
            if len(frees1[k]) > 1:
                message += "(* "
            for q in range(len(frees1[k]) - 1):
                message += frees1[k][q] + " "
            message += frees1[k][len(frees1[k]) - 1]
            if len(frees1[k]) == 1:
                message += " "
            else:
                message += ")"
        if len(frees1) > 1:
            message += ") "

        if len(frees2) > 1:
            message += "(+ "
        for k in range(len(frees2)):
            if len(frees2[k]) > 1:
                message += "(* "
            for q in range(len(frees2[k]) - 1):
                message += frees2[k][q] + " "
            message += frees2[k][len(frees2[k]) - 1]
            if len(frees2[k]) == 1 and k != len(frees2) - 1:
                message += " "
            if len(frees2[k]) != 1:
                message += ")"
        if len(frees2) > 1:
            message += ")"
        message += "))"
        message += "\n"
    message += "\n"

    amountofvars = 0

    for i in coefs:
        amountofvars += len(i)

    monotony = message.split("\n")
    for i in range(amountofvars + 1, len(monotony) - 1, 1):
        monotony[i] = monotony[i].replace("=", "")
        if monotony[i] != "":
            monotonous.append(monotony[i][8:len(monotony[i]) - 1])

    message += "(assert (and "
    for i in range(len(coefs)):
        for j in range(len(coefs[i]) - 1):
            message += "(>= " + coefs[i][j] + " 1) "
        message += "(>= " + coefs[i][len(coefs[i]) - 1] + " 0)"
        if i != len(coefs) - 1:
            message += " "
    message += "))\n\n"

    for i in range(len(third)):
        message += "(assert (or "
        if len(third[i]) > 1:
            message += "(and "
        for j in range(len(third[i]) - 1):
            message += third[i][j][8:len(third[i][j]) - 1].replace("=", "") + " "
        message += third[i][len(third[i]) - 1][8:len(third[i][len(third[i]) - 1]) - 1].replace("=", "")
        if len(third[i]) > 1:
            message += ")"
        message += " " + monotonous[len(monotonous) + i - rule] + "))\n"
    message += "\n"

    message += "(assert (and "
    for i in range(len(coefs)):
        message += "(or "
        if len(coefs[i]) > 2:
            message += "(and "
        for j in range(len(coefs[i]) - 1):
            message += "(> " + coefs[i][j] + " 1)"
            if j != len(coefs[i]) - 2 or (j == len(coefs[i]) - 2 and len(coefs[i]) == 2):
                message += " "
        if len(coefs[i]) > 2:
            message += ") "
        message += "(> " + coefs[i][len(coefs[i]) - 1] + " 0))"
        if i != len(coefs) - 1:
            message += " "
    message += "))\n\n"

    message += '''(check-sat)
(get-model)
(exit)'''

    f = open("stepa.smt2", "w")

    f.write(message)
    f.close()

    proc = subprocess.Popen("z3 -smt2 stepa.smt2", stdout=subprocess.PIPE, shell=True)
    (out, err) = proc.communicate()

    result = out.decode()

    print("\n", result)

    os.remove("isoev.smt2")


if __name__ == '__main__':
    print('Пример ввода: f(g(x, y)) -> g(x, y)\n'
          'Когда поступает пустая строка, ввод считается завершенным')
    main()
