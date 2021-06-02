import math
import random as rand


# Pre generated primes
first_primes_list = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29,
                     31, 37, 41, 43, 47, 53, 59, 61, 67,
                     71, 73, 79, 83, 89, 97, 101, 103,
                     107, 109, 113, 127, 131, 137, 139,
                     149, 151, 157, 163, 167, 173, 179,
                     181, 191, 193, 197, 199, 211, 223,
                     227, 229, 233, 239, 241, 251, 257,
                     263, 269, 271, 277, 281, 283, 293,
                     307, 311, 313, 317, 331, 337, 347, 349]


def power(a, b, c):
    # Implementation of repeated squaring modular exponentiation
    x = 1
    y = a
    while b > 0:
        if b & 1 != 0:
            x = (x * y) % c
        y = (y * y) % c
        b = int(b >> 1)
    return x % c


def millerRabin(n):
    # Implementation of the Miller - Rabin test
    # with k = 10 steps, thus producing an error less than 1/4^10
    s = 0
    t = n - 1
    while t & 1 == 0:
        # trying to write n - 1 = 2^s * t
        # building s
        t = t // 2
        s = s + 1
    k = 20
    for i in range(k):
        a = rand.randint(2, n - 1)
        x = power(a, t, n)
        # checking if the first element is 1 or -1
        if x == 1 or x == n - 1:
            continue
        for j in range(s):
            x = pow(x, 2) % n
            # if we get a -1, the next value will be a 1, so the algorithm ends
            # and tries with another base
            if x == n - 1:
                continue
        return False
    return True


def getLowLevelPrime(n):
    # Generate a prime candidate not divisible
    # by first primes
    while True:
        # Obtain a random number
        pc = rand.randrange(2 ** (n - 1) + 1, 2 ** n - 1)

        # Test divisibility by pre-generated
        # primes
        for divisor in first_primes_list:
            if pc % divisor == 0 and divisor ** 2 <= pc:
                break
        else:
            return pc


def genRandPrime(n):
    # creates a n-bit length number that isnt divisible by the primes
    # in the pregenerated list, then puts it to the Miller Rabin test
    # we test to see if we can get Sophie-Germain primes,and the safe prime associated
    # with that Sophie-Germain prime
    while True:
        prime_candidate = getLowLevelPrime(n)
        if not millerRabin(prime_candidate):
            continue
        else:
            if not millerRabin((prime_candidate - 1) // 2):
                continue
            else:
                return (prime_candidate - 1) // 2


def menu():
    #Prints a interactive menu
    print("1. Generate keys")
    print("2. Show keys")
    print("3. Encrypt")
    print("4. Decrypt")
    print("5. Show available ciphers")
    print("6. Exit")


def gen_keys():
    # generates a public and private key
    p = genRandPrime(256)
    # generates a Sophie-Germain prime of 256 bits
    g = 0
    q = p
    # the associated safe prime
    p = 2 * q + 1
    # using our safe prime,we test for a generator
    found = False
    while not found:
        g = rand.randint(2, p - 1)
        if pow(g, 2) % p != 1 and power(g, q, p) != 1:
            found = True
    a = rand.randint(2, p - 2)
    ga = power(g, a, p)
    publ = (p, g, ga)
    priv = a
    return publ, priv


def breakIntoChunks(msg, size):
    # breaks a string into chunks, with a given bound for the chunk size
    # it splits the message into chunks s.t. each chunk contains full bytes
    chunks = []
    i = 0
    diff = math.floor(size // 8)
    diff = diff*8
    while i < len(msg):
        chunks.append(msg[i : i + diff])
        i = i + diff
    return chunks


def StringToBin(msg):
    # returns the binary representation of a given string
    # by iterating through the string and saving the binary representation
    # for each character
    m = ""
    for letter in msg:
        aux = str(bin(ord(letter)))[2:]
        # adds 0's in front so that the byte is complete
        while len(aux) != 8:
            aux = "0" + aux
        m = m + aux
    return m


def BinToString(msg):
    # gets a binary string and splits it into chunks of 8
    # and then transforms each byte into the corresponding letter
    m = ""
    # adds 0 in front if the given length is not divisible by 8
    while len(msg) % 8 != 0:
        msg = "0" + msg
    for i in range(0, len(msg), 8):
        aux = msg[i:i + 8]
        aux = int(aux, 2)
        aux = chr(aux)
        m = m + aux
    return m


def encrypt(msg, p, g, ga):
    k = rand.randint(2, p - 2) # generates k
    # represent the message m in binary
    # takes the binary ascii code of each character in the messages
    # and concatenates them into a big long string
    m = StringToBin(msg)
    binMsg = m
    m = int(m, 2) # gets the decimal value of that
    alfa = power(g, k, p)
    beta = [] # beta is made a list in case there's a need to split the
    # message into chunks and encrypt them individually
    # since beta carries the message into the ciphertext
    aux = power(ga, k, p)
    if m > p:
        chunks = breakIntoChunks(binMsg, p.bit_length())
        # encrypt each chunk individually
        for chunk in chunks:
            beta.append(int(chunk, 2) * aux % p)
        return alfa, beta
    beta.append(m * aux % p)
    return alfa, beta


def decrypt(alfa, beta, p, a):
    # gets the inverse mod p of alfa
    inv = inverseModN(alfa, p)
    #calculates alfa ^ -a mod p
    newAlfa = power(inv, a, p)
    # if there was no need for chunking
    if len(beta) == 1:
        m = newAlfa * beta[0]
        # gets the original message and reduce it mod p
        m = m % p
        m = str(bin(m))[2:]
        # converts m to binary and splits it in chunks of 7 bits
        # each chunk represents a character, hence the original message is decoded and reproduced
        msg = BinToString(m)
        return msg
    else:
        # if the message was split into chunks
        # decrypt each chunk individually, turn it into binary
        # and concatenate it to get the original message
        # in binary representation
        msg = ""
        for i in range(len(beta)):
            m = newAlfa * beta[i]
            m = m % p
            aux = str(bin(m))[2:]
            # if the binary representation isnt a multiple of 8, add 0's in front
            while len(aux) % 8 != 0:
                aux = "0" + aux
            msg = msg + aux
        return BinToString(msg)


def inverseModN(a, b):
    # calculates the inverse of a mod b
    return 0 if a == 0 else 1 if b % a == 0 else b - inverseModN(b % a, a) * b // a


def main():
    # main function of the program
    keys = [] # list of generated keys
    ciphers = [] # list of generated ciphers
    opt = ""
    while opt != "6":
        menu()
        opt = input("Option: ")
        if opt == "1":
            ok = False
            name = input("Name : ")
            for key in keys:
                if key[0] == name:
                    print("That name already exists!")
                    ok = True
            if ok:
                continue
            print("Generating keys...This shouldn't take long.")
            publ, priv = gen_keys()
            keys.append((name, publ, priv))
            print("Public key : (" + str(publ[0]) + ", " + str(publ[1]) + ", " + str(publ[2]) + ")")
            print("Private key : " + str(priv))
        elif opt == "2":
            for elem in keys:
                print("Name : " + str(elem[0]))
                print("Public key : (" + str(elem[1][0]) + ", " + str(elem[1][1]) + ", " + str(elem[1][2]) + ")")
                print("Private key : " + str(elem[2]))
        elif opt == "3":
            name = input("Enter name from whom to take public key: ")
            p = 0
            g = 0
            ga = 0
            ok = False
            for key in keys:
                if key[0] == name:
                    p = key[1][0]
                    g = key[1][1]
                    ga = key[1][2]
                    ok = True
                    break
            if not ok:
                print("That person doesnt have any keys generated!")
                continue
            msg = input("Enter message: ")
            c1, c2 = encrypt(msg, p, g, ga)
            ciphers.append((c1, c2, name))
            print("Public key used: (" + str(p) + ", " + str(g) + ", " + str(ga) + ")")
            print("Cipher-text : (" + str(c1) + ", " + str(c2) + ")")
        elif opt == "4":
            index = int(input("Give the index for the cipher you want to decrypt(the number they have when printed out) : "))
            if index >= len(ciphers) or index < 0:
                print("Incorrect index!")
                continue
            cipher = ciphers[index]
            name = cipher[2]
            p = 0
            a = 0
            for key in keys:
                if key[0] == name:
                    p = key[1][0]
                    a = key[2]
                    break
            print("Private key used : " + str(a))
            print("Key belongs to : " + name)
            msg = decrypt(cipher[0], cipher[1], p, a)
            print("Original message: " + msg)
        elif opt == "5":
            i = 0
            for cipher in ciphers:
                print("c" + str(i) + " = (" + str(cipher[0]) +", " + str(cipher[1]) + ") - encypted with " + cipher[2] + "'s public key")
                i = i + 1
        elif opt == "6":
            print("Bye bye!")
        elif opt != "6":
            print("Wrong option!")


if __name__ == "__main__":
    main()

