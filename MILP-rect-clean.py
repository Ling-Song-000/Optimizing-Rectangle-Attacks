# this is the clean version for our AC paper by deleting unused functions
# including the codes for Serpent and Skinny

from functools import reduce
import math
import random

from gurobipy import *

class BasicTools:

    def __init__(self):
        pass

    @staticmethod
    def getVariables_From_Constraints(self, C):
        V = set([])
        for s in C:
            temp = s.strip()
            temp = temp.replace('+', ' ')
            temp = temp.replace('-', ' ')
            temp = temp.replace('>=', ' ')
            temp = temp.replace('<=', ' ')
            temp = temp.replace('=', ' ')
            temp = temp.split()
            for v in temp:
                if not v.isdigit():
                    V.add(v)
        return V

    def writeFile(self, name, objfunc, C, BV, GV):
        f = open(name, 'w')
        f.write('Minimize\n')

        f.writelines(objfunc)
        f.write('\n\n')
        f.write('Subject To\n')
        for c in C:
            f.write(c)
            f.write('\n')
        f.write('\n')
        f.write('Binary\n')
        for v in BV:
            f.write(v)
            f.write('\n')
        if len(GV) > 0:
            f.write('\n')
            f.write('General\n')
            for v in GV:
                f.write(v)
                f.write('\n')     
        f.write('End\n')  
        f.close()


class ConstraintGenerator:
    def __init__(self):
        pass

    @staticmethod
    def genFromConstraintTemplate(self, in_vars, out_vars, ineq_template):
        """
        Example:
            >>> ConstraintGenerator.genFromConstraintTemplate(['x0', 'x1'], ['y0'], [(-1, 2, 3, 1), (1, -1, 0, -2)] )
            ['-1 x0 + 2 x1 + 3 y0 >= - 1', '1 x0 - 1 x1 + 0 y0 >= 2']
            >>> ConstraintGenerator.genFromConstraintTemplate(['x0', 'x1'], ['y0'], [(-1, 2, 3, 1), (-1, -1, 0, -2)] )
            ['-1 x0 + 2 x1 + 3 y0 >= - 1', '-1 x0 - 1 x1 + 0 y0 >= 2']
        """
        assert ineq_template != list([])
        assert (len(in_vars) + len(out_vars)) == (len(ineq_template[1]) - 1)

        vars_list = in_vars + out_vars
        constraints = list([])
        for T in ineq_template:
            s = str(T[0]) + ' ' + in_vars[0]
            for j in range(1, len(vars_list)):
                if T[j] >= 0:
                    s = s + ' + ' + str(T[j]) + ' ' + vars_list[j]
                elif T[j] < 0:
                    s = s + ' - ' + str(-T[j]) + ' ' + vars_list[j]

            s = s + ' >= '
            if T[-1] <= 0:
                s = s + str(-T[-1])
            elif T[-1] > 0:
                s = s + '- ' + str(T[-1])

            constraints.append(s)

        return constraints
    
    def assign(self, var, value):
        return var + ' = ' + str(value)


class SERPENT(BasicTools, ConstraintGenerator):
    def __init__(self, p,  lb,ld, lf):
        self.initialization(p,  lb, ld, lf)
        BasicTools.__init__(self)
        ConstraintGenerator.__init__(self)
        
    def initialization(self, p,  lb, ld, lf):
        self.cell = 4
        self.n = 128
        self.p = p
        self.D = 64 + p
        print(str(254-self.D))
        a0 = 0b00100000000000001001001000000000 
        a1 = 0b00000000000000000001000000000000
        a2 = 0b00100000000000010000000000000000
        a3 = 0b00100000000000010000001000000000
        w0 = 0b00000000000000000000000000000000 
        w1 = 0b00000010000000000000000000000000
        w2 = 0b00000000000000000000000000000000
        w3 = 0b00000010000000000000000000000000
        self.din = self.linear_transformation_inv( (a0, a1, a2, a3) )
        self.dout = self.linear_transformation(  (w0, w1, w2, w3) ) 
        self.lb = lb
        self.ld = ld
        self.lf = lf
        self.Diff = self.generateVar('s')
        self.Fix = self.generateVar('f')
        self.Value = self.generateVar('m')
        self.Dtm_i = self.generateVar('di')
        self.Dtm_o = self.generateVar('do')
        self.Verif = self.generateVar('v')
        self.UsedKey = self.generateVar('uk')
        self.GuessedKey = self.generateVar('gk')
        self.TV = ['T', 'T1', 'T2', 'T3']
        self.isB = 0
        
        
    def generateVar(self, s):  
        ret = [[s+'_r'+str(i)+'_'+str(j) for j in range(int(self.n/self.cell))] for i in range(self.lb)]
        ret += [[s+'_r'+str(i)+'_'+str(j) for j in range(int(self.n/self.cell))] for i in range(self.lb+self.ld, self.lb+self.ld+self.lf)] 
        return ret
  
    def diffPropagation(self):
        constr = []
        for r in [self.lb-1]:
            w0, w1, w2, w3 = self.din
            row = w0 | w1 | w2 | w3
            for i in range(32):
                ASi = (row>>i) & 0x1  
                constr.append(self.assign(self.Diff[r][i], ASi))
                constr.append(self.assign(self.Fix[r][i], 1))
        for r in [self.lb + self.lf - 1]:
            w0, w1, w2, w3 = self.dout
            row = w0 | w1 | w2 | w3
            for i in range(32):
                ASi = (row>>i) & 0x1  
                constr.append(self.assign(self.Diff[r][i], ASi))
                constr.append(self.assign(self.Fix[r][i], 1))      
        return constr
 
    def verificationPath(self):
        constr = []
        for r in [self.lb-1]:
            w0, w1, w2, w3 = self.din
            row = w0 | w1 | w2 | w3
            for i in range(32):
                ASi = (row>>i) & 0x1  
                constr.append(self.assign(self.UsedKey[r][i], ASi))
        for r in [self.lb + self.lf - 1]:
            w0, w1, w2, w3 = self.dout
            row = w0 | w1 | w2 | w3
            for i in range(32):
                ASi = (row>>i) & 0x1  
                constr.append(self.assign(self.UsedKey[r][i], ASi))   
        return constr                                                            

    def guessAndDetermine(self):
        """
        di uk gk do       do f v
        0  0  0  0        1  1 1
        0  1  0  0        0  1 0
        1  0  0  0        1  0 0
        1  1  0  0        0  0 0
        1  1  1  1
        di - do >= 0
        uk - gk >= 0
        """
        tmp = [(1, 0, -1, 0), (-1, -1, 1, 1), (0, 1, -1, 0)]
        constr = []
        for r in [0]:# plaintext is known
            for i in range(32):
                constr.append(self.assign(self.Dtm_i[r][i], 1))
        for r in [self.lb + self.lf - 1]: # ciphertext is known
            for i in range(32):
                constr.append(self.assign(self.Dtm_o[r][i], 1))       
        for r in [0]:
            for i in range(32):
                constr.append("%s - %s >= 0" % (self.Dtm_i[r][i], self.Dtm_o[r][i]))
                constr.append("%s - %s >= 0" % (self.UsedKey[r][i], self.GuessedKey[r][i]))
                constr.append("%s - %s = 0" % (self.Dtm_o[r][i], self.GuessedKey[r][i]))  
                constr += self.genFromConstraintTemplate(self, [self.Dtm_o[r][i],self.Fix[r][i]], [self.Verif[r][i]], tmp )

        for r in [self.lb + self.lf - 1]: 
            for i in range(32):        
                constr.append("%s - %s >= 0" % (self.Dtm_o[r][i], self.Dtm_i[r][i]))
                constr.append("%s - %s >= 0" % (self.UsedKey[r][i], self.GuessedKey[r][i]))
                constr.append("%s - %s = 0" % (self.Dtm_i[r][i], self.GuessedKey[r][i]))
                constr += self.genFromConstraintTemplate(self, [self.Dtm_i[r][i],self.Fix[r][i]], [self.Verif[r][i]], tmp )

        return constr
    
    def defineComplexity(self):
        constr = []
        list_gkb = []
        list_rb = []
        list_vb = []
        for r in range(self.lb):
            list_gkb += self.GuessedKey[r]
            list_rb += self.Diff[r]
            list_vb += self.Verif[r]
        list_gkf = []
        list_rf = []
        list_vf = []
        for r in range(self.lb, self.lb + self.lf):
            list_gkf += self.GuessedKey[r]
            list_rf += self.Diff[r]      
            list_vf += self.Verif[r]
        minus_gk = ' - 4 ' + ' - 4 '.join(list_gkb + list_gkf)
        constr.append("%s%s >= %s" %(self.TV[1], minus_gk, str(self.D+1)))
        rbp = ' + 4 '+' + 4 '.join(list_vb)
        rfp = ' + 4 '+' + 4 '.join(list_vf)
        rfp2 = ' + 8 '+' + 8 '.join(list_vf)        
        rbp2 = ' + 8 '+' + 8 '.join(list_vb)
        minus_rf =  ' - 4 '+' - 4 '.join(list_rf)
        minus_rb =  ' - 4 '+' - 4 '.join(list_rb)
        minus_rf2 = ' - 8 ' + ' - 8 '.join(list_rf)
        minus_rb2 = ' - 8 ' + ' - 8 '.join(list_rb)
        if self.isB == 1:
            minus_T2 = minus_gk  + minus_rb + rbp 
            constr.append("%s%s >= %2f" %(self.TV[2], minus_T2, self.D - 1 ))
        else:
            minus_T2 = minus_gk  + minus_rf + rfp  
            constr.append("%s%s >= %2f" %(self.TV[2], minus_T2, self.D*2-self.n - 1 ))
        minus_T3 = minus_gk + minus_rb2 + minus_rf2 + rbp2 + rfp2
        constr.append("%s%s >= %2f" %(self.TV[3], minus_T3, self.D*2 - 2*self.n - 2))
        constr.append("%s - %s >= 0" %(self.TV[0], self.TV[1]))
        constr.append("%s - %s >= 0" %(self.TV[0], self.TV[2]))  
        constr.append("%s - %s >= 0" %(self.TV[0], self.TV[3]))
        return constr
    
    def genObj(self):
        return self.TV[0]
    
    def readSol(self, filename):
        solFile = open(filename,'r')
        var_value_map = dict()
        for line in solFile:
            if line[0] != '#':
                temp = line
                temp = temp.split()
                var_value_map[temp[0]] = int(temp[1])
        list_gkb = []
        list_rb = []
        list_vb = []
        for r in range(self.lb):
            list_gkb += self.GuessedKey[r]
            list_rb += self.Diff[r]
            list_vb += self.Verif[r]
        list_gkf = []
        list_rf = []
        list_vf = []
        for r in range(self.lb, self.lb + self.lf):
            list_gkf += self.GuessedKey[r]
            list_rf += self.Diff[r]      
            list_vf += self.Verif[r] 
        rb = 0
        for v in list_rb:
            rb += var_value_map[v]
        print("rb = %d" %rb)
        rf = 0
        for v in list_rf:
            rf += var_value_map[v]
        print("rf = %d" %rf)
  
        gkb = 0
        for v in list_gkb:
            gkb += var_value_map[v]
        print("gkb = %d" %gkb)
        gkf = 0
        for v in list_gkf:
            gkf += var_value_map[v]
        print("gkf = %d" %gkf)
        
        
    def rotate_left(self, word, count):
        return ((word << count) | (word >> (32 - count))) & 0xffffffff
    
    def rotate_right(self, word, count):
        return ((word << (32 - count)) | (word >> count)) & 0xffffffff
    
    def word2vector(self, word): #v[i] = W_i
        v = []
        for i in range(32):
            v.append( (word>>i)& 0x1)
        return v
    
    def vector2word(self, v):
        w = 0
        for i in range(32):
            w = w^( (v[i]&0x1)<<i )
        return w
        
    def blockword2vector(self, block_words):
        w0, w1, w2, w3 = block_words
        v = self.word2vector(w0)
        v += self.word2vector(w1)
        v += self.word2vector(w2)
        v += self.word2vector(w3)
        return v
    
    def vector2blockwords(self, v):
        w0 = self.vector2word(v[0:32])
        w1 = self.vector2word(v[32:64])
        w2 = self.vector2word(v[64:96])
        w3 = self.vector2word(v[96:128])
        return w0, w1, w2, w3
        
    def linear_transformation(self, block_words):
        w0, w1, w2, w3 = block_words
        w0 = self.rotate_left(w0, 13)
        w2 = self.rotate_left(w2, 3)
        w1 ^= w0 ^ w2
        w3 ^= w2 ^ ((w0 << 3) & 0xffffffff)
        w1 = self.rotate_left(w1, 1)
        w3 = self.rotate_left(w3, 7)
        w0 ^= w1 ^ w3
        w2 ^= w3 ^ ((w1 << 7) & 0xffffffff)
        w0 = self.rotate_left(w0, 5)
        w2 = self.rotate_left(w2, 22)
        return w0, w1, w2, w3
    	
    def linear_transformation_inv(self, block_words):
        w0, w1, w2, w3 = block_words
        w2 = self.rotate_right(w2, 22)	
        w0 = self.rotate_right(w0, 5)	
        w2 ^= w3 ^ ((w1 << 7) & 0xffffffff)	
        w0 ^= w1 ^ w3	
        w3 = self.rotate_right(w3, 7)	
        w1 = self.rotate_right(w1, 1)	
        w3 ^= w2 ^ ((w0 << 3) & 0xffffffff)	
        w1 ^= w0 ^ w2	
        w2 = self.rotate_right(w2, 3)	
        w0 = self.rotate_right(w0, 13)
        return w0, w1, w2, w3

    def getMatrixInv(self):
        M = [[0 for i in range(128)] for j in range(128)]
        for i in range(128):
            v = [0 for j in range(128)]
            v[i] = 1
            w0, w1, w2, w3 = self.vector2blockwords(v)
            w0, w1, w2, w3 = self.linear_transformation_inv( (w0, w1, w2, w3) )
            u = self.blockword2vector( (w0, w1, w2, w3) )
            for j in range(128):
                M[j][i] = u[j]
        return M

    def nAS(block_words):
        w0, w1, w2, w3 = block_words
        row = w0 | w1 | w2 | w3
        num = 0
        for i in range(32):
            num += (row>>i) & 0x1
        return num
    def genModel(self):
        C = list([])
        C += self.diffPropagation()
        C += self.verificationPath()
        C += self.guessAndDetermine()


        BV = self.getVariables_From_Constraints(self, C)
        C += self.defineComplexity()
        GV = self.TV
        obj = self.genObj()

        name = 'serpent'
        self.writeFile(name + '.lp', obj, C, BV, GV)
        m = read(name + '.lp')
        m.optimize()
        m.write(name+'.sol')
        self.readSol(name+'.sol')
        
class SKINNY(BasicTools, ConstraintGenerator):
    def __init__(self, cell, Z, p,  lb,ld, lf, isB):
        self.initialization(cell, Z, p,  lb, ld, lf, isB)
        BasicTools.__init__(self)
        ConstraintGenerator.__init__(self)
        
    def initialization(self, n, Z, p,  lb, ld, lf, isB):
        self.cell = int(n/16)
        self.isB = isB   # isB = 1 means forming pairs on plaintext, otherwise, forming pairs on ciphertexts
        self.nCell = 16
        self.n = n
        self.p = p # the boomerang's prob is P^2 = 2^-2p, i.e., p is a ptositive number
        self.D = (self.n/2) + p # + 2  2 for 4 related keys

        self.z = Z
        self.lb = lb # len of E_b
        self.ld = ld # len of distinguisher
        self.lf = lf # len of E_f
        # for difference propagation
        self.Diff = self.generateVar('sb') # mark acitve bytes of SB
        self.DiffATK = self.generateVar('sk') # mark acitve bytes after ATK
        self.Fix = self.generateVar('f')  # mark the byete with fixed difference, including 0 difference 
        self.Value = self.generateVar('m') # the value needs to be known for verifying the distinguisher, haven't used in the end
        # for value verification
        self.UsedKey = self.generateVar('uk') # subkey bytes used for verifying the distinguisher, the last 8 bytes are 0
        self.UK0 = ['uk0_' + str(i) for i in range(self.nCell) ]  # use equivalent stk for the first round, the last 8 bytes may be nonzero
        self.UKreal16 = ['ukr' + str(i) for i in range(self.nCell)] # one var for a lane taking values from 0 to z
        self.UKlaneSum16 = ['uks' + str(i) for i in range(self.nCell)] # one var for a lane taking values from 0 to ..
        # for guess-and-determine
        # variables to denote if the byte is dtermined or not: xi --> ATK --> Yi --> SR,MC --> zi --> SB --> xi+1
        self.Dtm_x = self.generateVar('dx') # if the output of SB is determined
        self.Dtm_y = self.generateVar('dy') # if the output of ATK is dtermined         
        self.Dtm_z = self.generateVar('dz') # if the output of SR,MC is dtermined     
        self.Diff_dtm = self.generateVar('dd') # if the diff_out (resp. diff_in) of an Sbox is determined (=const/0) in E_b (resp. E_f)
        self.Verif = self.generateVar('v') # if an inner condition is verified under guessed key bits, used for counting r'_b and r'_f        
        self.GuessedKey = self.generateVar('gk') # gk = 1 if that key byte is guessed, the last 8 bytes are 0
        self.GK0 = ['gk0_' + str(i) for i in range(self.nCell) ] # use equivalent stk for the first round,the last 8 bytes may be nonzero
        self.GKreal16 = ['gkr' + str(i) for i in range(self.nCell)] # one var for a lane taking values from 0 to z
        self.GKlaneSum16 = ['gks' + str(i) for i in range(self.nCell)] # one var for a lane taking values from 0 to ..
        # model the complexity
        self.TV = ['T', 'T1', 'T2', 'T3'] # time complexities
        self.M = [ [1, 0, 1, 1],\
                   [1, 0, 0, 0],\
                   [0, 1, 1, 0],\
                   [1, 0, 1, 0]]
        self.Minv = [[0, 1, 0, 0],\
                     [0, 1, 1, 1],\
                     [0, 1, 0, 1],\
                     [1, 0, 0, 1]]
        self.PT = [9, 15, 8, 13, 10, 14, 12, 11, 0, 1, 2, 3, 4, 5, 6, 7]
        self.PTI = [8,9,10,11,12,13,14,15,2,0,4,7,6,3,5,1]
        self.din = [] # exact diff before the first S-box layer of dist.
        self.dout = [] # exact diff after the last MC of the dist.
        self.DK1 = [] # active pattern at the beginning of the distinguisher
        self.DK2 = [] # active pattern at the beginning of the distinguisher
        listk = [i for i in range(16)]
        for i in range(32):
            print("round",i, listk)
            listk = self.nextTKpattern(listk)
        if n == 128 and self.z == 3 and self.ld == 23:
            self.din = [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0, 0x20] 
            self.dout = [0, 0, 0, 0,  0, 0, 0, 0,  0, 0x50, 0, 0, 0, 0, 0, 0]
            self.DK1 = [0,0,0,0,0,0,0,0, 1,0,0,0,0,0,0,0] 
            self.DK2 = [0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0] 
        # below 22-round dist of skinny-64-192, EC'12
        if n == 64 and self.z == 3 and self.ld == 22:
            self.din = [1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0] 
            self.dout = [0, 0, 0, 0, 0, 0, 0, 0, 0, 0xa, 0, 0, 0, 0, 0, 0]
            self.DK1 = [1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1] 
            self.DK2 = [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0]    
        if n == 64 and self.z == 2 and self.ld == 18:                         
            self.din = [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2 ] 
            self.dout = [0,0,0xd,0, 0,0,0xd,0, 0,0,0,0, 0,0,0xd,0]
            self.DK1 = [0,0,1,0, 0,0,0,0, 0,0,0,0, 1,0,0,0 ] 
            self.DK2 = [0,0,0,0, 0,0,0,0, 1,0,0,0, 0,0,0,0]  
        if n == 128 and self.z == 2 and self.ld == 18:
            self.din = [00, 00, 2, 00, 00, 00, 00, 00, 00, 00, 00, 00, 00, 00, 00, 00] 
            self.dout = [00, 00, 0x37, 00,  00, 00, 0x37, 00,  00, 00, 00, 00,  00, 00, 0x37, 00 ] # 原文表格最后一个37位置错了
            self.DK1 = [00, 00, 1, 00, 00, 00, 00, 00, 00, 00, 00, 00, 00, 00, 00, 00 ] 
            self.DK2 = [00, 00, 00, 00, 00, 00, 00, 00, 1, 00, 00, 00, 00, 00, 00, 00 ]              
        if n == 128 and self.z == 2 and self.ld == 19:
            self.din =  [0xcb, 00, 00, 00,  00, 00, 00, 0xcb,  00, 00, 0xcb, 00,  00, 00, 00, 00] 
            self.dout = [00, 00, 0x81, 00,  00, 00, 0x81, 00,  00, 00, 00, 00,  00, 00, 81, 00] # 原文表格最后一个81位置错了
            self.DK1 = [00, 00, 00, 00, 00, 00, 00, 00, 00, 00, 1, 00, 00, 00, 00, 00] 
            self.DK2 = [1, 00, 00, 00, 00, 00, 00, 00, 00, 00, 00, 00, 00, 00, 00, 00]          
    def generateVar(self, s):  
        ret = [[s+'_r'+str(i)+'_'+str(j) for j in range(int(self.n/self.cell))] for i in range(self.lb)]
        ret += [[s+'_r'+str(i)+'_'+str(j) for j in range(int(self.n/self.cell))] for i in range(self.lb+self.ld, self.lb+self.ld+self.lf)] 
        return ret
    

    def MixColumn(self, vect): # vect is a vector of 16 cells
        ret = [None for i in range( int(self.nCell) )]
        for col in range(4):
            for row in range(4):
                v = 0
                for i in range(4):
                    v ^= self.M[row][i]*vect[4*i + col]
                ret[4*row + col] = v
        return ret

    def activePatternMC(self, vect): # vect is a vector of 0/1
        """
        truncated pattern propagates through MC with prob = 1
        """
        ret = [None for i in range( int(self.n/self.cell) )]
        for col in range(4):
            for row in range(4):
                v = 0
                for i in range(4):
                    v |= self.M[row][i]*vect[4*i + col]
                ret[4*row + col] = v
        return ret   

    def valuePatternMC(self, vect): # vect is a vector of 0/1
        """
        y = MC*x
        vect is the pattern of of y where vect[i]= 1 means the value of the i-th byte is needed.
        """
        ret = [0 for i in range( int(self.n/self.cell) )]
        for col in range(4):
            for row in range(4):
                if vect[4*row + col] == 1:
                    for i in range(4):
                        ret[4*i + col] |= self.M[row][i]
        return ret 
    
    def MixColumnInv(self, vect): # vect is a vector of 16 cells
        ret = [None for i in range( int(self.n/self.cell) )]
        for col in range(4):
            for row in range(4):
                v = 0
                for i in range(4):
                    v ^= self.Minv[row][i]*vect[4*i + col]
                ret[4*row + col] = v
        return ret
  
    def activePatternMCinv(self, vect): # vect is a vector of 0/1
        """
        truncated pattern propagates through MCinv with prob = 1
        """
        ret = [None for i in range( int(self.n/self.cell) )]
        for col in range(4):
            for row in range(4):
                v = 0
                for i in range(4):
                    v |= self.Minv[row][i]*vect[4*i + col]
                ret[4*row + col] = v
        return ret  

    def valuePatternMCinv(self, vect): # vect is a vector of 0/1
        """
        x = MCinv*y
        vect is the pattern of of x where vect[i]= 1 means the value of the i-th byte is needed.
        """
        ret = [0 for i in range( int(self.n/self.cell) )]
        for col in range(4):
            for row in range(4):
                if vect[4*row + col] == 1:
                    for i in range(4):
                        ret[4*i + col] |= self.Minv[row][i]
        return ret 
    
    def perm(self, vect, P):
        """
        vect is a vector of 0/1
        P is a permuation
        """
        ret = [None for i in range( int(self.n/self.cell) )]
        for i in range( int(self.n/self.cell) ):
            ret[i] = vect[P[i]]
        return ret
    
    def SR(self, vect):
        P = [0,1,2,3,7,4,5,6,10,11,8,9,13,14,15,12]
        return self.perm(vect, P)
    
    def SRinv(self, vect):
        P = [0,1,2,3,5,6,7,4,10,11,8,9,15,12,13,14]
        return self.perm(vect, P)      

    def constrValueMCorInv(self, inpt, oput, MC):
        """
        all inputs are known => output is known
        may need more constraints
        """
        constr = []
        for col in range(4):
            for row in range(4):
                ls = []
                for i in range(4):
                    if MC[row][i]:
                        ls.append(inpt[4*i+col])
                constr.append("%s - %d %s >= 0" %(' + '.join(ls), len(ls), oput[4*row+col]))
        return constr

    def constrConditionMCorInv(self, iput, oput, deter, fix, veri, MC):
        """
        y = MC*x
        iput denotes the activeness of x
        oput denotes the activeness of y
        deter denotes if the state byte is determined or not, ie the exact value is known or not
        veri to mark if a byte condition is verified or not
        """
        # active1 dtermine1 activeout fix verified
        temp1 = [(1, 0, 1, -1, -1), (-1, -1, -1, 1, 2), (0, 1, 0, -1, 0)]
        # active1, determine1, active2, determine2, activeoutput, fix, verified
        temp2 = [(1, 0, 1, 0, 1, 2, -2, -2), (-1, 2, 1, 0, 1, 0, -2, 0), (1, 0, -1, 2, 1, 0, -2, 0),\
                 (1, 0, -1, -1, 0, -1, 1, 2), (1, 0, 1, 0, -1, 0, 0, 0), (-1, -1, 0, -1, 0, -1, 1, 3),\
                 (0, 0, 0, 0, 1, 1, 0, -1), (-1, -1, 1, 0, 0, -1, 1, 2)]

        # active1, determine1, active2, determine2, active3, determine3, activeoutput, fix, verified
        temp3 = [(1, 0, 1, 0, 1, 0, 1, 2, -2, -2),(-1, 1, 0, 0, 0, 0, 0, 0, -1, 1),(0, 0, 0, 0, 0, 0, 1, 1, 0, -1),\
                 (0, 0, -1, 1, 0, 0, 0, 0, -1, 1),(1, 0, 1, 0, -1, 2, 1, 0, -2, 0),(0, -1, 1, 0, -1, -1, 0, -1, 1, 3),\
                 (-1, 0, 1, 0, 1, 0, 1, 0, 0, 0),(0, -1, -1, -1, 1, 0, 0, -1, 1, 3),(0, -1, 1, 0, 1, 0, -1, -1, 1, 2),\
                 (1, 0, -1, -1, 0, -1, 0, -1, 1, 3),(1, 0, -1, 0, 1, 0, 1, 0, 0, 0),(1, 0, 1, 0, 1, 0, -1, 0, 0, 0),\
                 (1, 0, 1, 0, -1, -1, 0, -1, 1, 2),(-1, -1, 0, -1, 0, -1, 0, -1, 1, 4),(0, 0, 0, 0, 0, 0, 0, 1, -1, 0),\
                 (1, 0, -1, -1, 1, 0, 0, -1, 1, 2),(0, 0, 0, 0, -1, 1, 0, 0, -1, 1)  ]
        constr = []
        for col in range(4):
            for row in range(4):
                ls = []
                for i in range(4):
                    if MC[row][i]:
                        ls.append(iput[4*i+col])
                        ls.append(deter[4*i+col])
                if len(ls) == 4:
                    #print(fix)
                    constr += self.genFromConstraintTemplate(self, ls, [oput[4*row+col], fix[4*row+col], veri[4*row+col]], temp2 )                
                if len(ls) == 6:
                    constr += self.genFromConstraintTemplate(self, ls, [oput[4*row+col], fix[4*row+col], veri[4*row+col]], temp3 )    
                if len(ls) == 2:
                    constr.append("%s - %s >= 0" %(ls[0], oput[4*row+col]))
                    constr.append("%s - %s <= 0" %(ls[0], oput[4*row+col]))
                    constr += self.genFromConstraintTemplate(self, ls, [ fix[4*row+col], veri[4*row+col]], temp1 ) 
        return constr

    def constrConditionMC(self, iput, oput, deteri, detero, fix, veri):
        """
        y = MC*x
        iput denotes the activeness of x
        oput denotes the activeness of y
        y0 = y3 + x3
        y1 = x0
        y2 = x1 + x3
        y3 = x0 + x2
        """
        # active1 dtermine1 activeout fix verified
        temp1 = [(1, 0, 1, -1, -1), (-1, -1, -1, 1, 2), (0, 1, 0, -1, 0)]
        # active1, determine1, active2, determine2, activeoutput, fix, verified
        temp2 = [(1, 0, 1, 0, 1, 2, -2, -2), (-1, 2, 1, 0, 1, 0, -2, 0), (1, 0, -1, 2, 1, 0, -2, 0),\
                 (1, 0, -1, -1, 0, -1, 1, 2), (1, 0, 1, 0, -1, 0, 0, 0), (-1, -1, 0, -1, 0, -1, 1, 3),\
                 (0, 0, 0, 0, 1, 1, 0, -1), (-1, -1, 1, 0, 0, -1, 1, 2)]

        constr = []
        for col in range(4):
            for row in range(4):
                ls = []                
                if row == 0: # for y0
                    ls.append(iput[4*3+col]); ls.append(deteri[4*3+col])
                    ls.append(oput[4*3+col]); ls.append(detero[4*3+col])
                else:           
                    for i in range(4):
                        if self.M[row][i]:
                            ls.append(iput[4*i+col])
                            ls.append(deteri[4*i+col])
                if len(ls) == 4:
                    #print(fix)
                    constr += self.genFromConstraintTemplate(self, ls, [oput[4*row+col], fix[4*row+col], veri[4*row+col]], temp2 )                
                if len(ls) == 6:
                    print('bug')
                    #constr += self.genFromConstraintTemplate(self, ls, [oput[4*row+col], fix[4*row+col], veri[4*row+col]], temp3 )    
                if len(ls) == 2:
                    constr.append("%s - %s >= 0" %(ls[0], oput[4*row+col]))
                    constr.append("%s - %s <= 0" %(ls[0], oput[4*row+col]))
                    constr += self.genFromConstraintTemplate(self, ls, [ fix[4*row+col], veri[4*row+col]], temp1 ) 
        return constr

    def constrConditionMCinv(self, iput, oput, deteri, detero, fix, veri):
        """
        x = MCinv*y
        iput denotes the activeness of y
        oput denotes the activeness of x
        x0 = y1
        x1 = y1 + y2 + y3 = x2 + y2
        x2 = y1 + y3
        x3 = y0 + y3
        """
        # active1 dtermine1 activeout fix verified
        temp1 = [(1, 0, 1, -1, -1), (-1, -1, -1, 1, 2), (0, 1, 0, -1, 0)]
        # active1, determine1, active2, determine2, activeoutput, fix, verified
        temp2 = [(1, 0, 1, 0, 1, 2, -2, -2), (-1, 2, 1, 0, 1, 0, -2, 0), (1, 0, -1, 2, 1, 0, -2, 0),\
                 (1, 0, -1, -1, 0, -1, 1, 2), (1, 0, 1, 0, -1, 0, 0, 0), (-1, -1, 0, -1, 0, -1, 1, 3),\
                 (0, 0, 0, 0, 1, 1, 0, -1), (-1, -1, 1, 0, 0, -1, 1, 2)]

        constr = []
        for col in range(4):
            for row in range(4):
                ls = []                
                if row == 1: # for x1
                    ls.append(iput[4*2+col]); ls.append(deteri[4*2+col])
                    ls.append(oput[4*2+col]); ls.append(detero[4*2+col])
                else:           
                    for i in range(4):
                        if self.Minv[row][i]:
                            ls.append(iput[4*i+col])
                            ls.append(deteri[4*i+col])
                if len(ls) == 4:
                    #print(fix)
                    constr += self.genFromConstraintTemplate(self, ls, [oput[4*row+col], fix[4*row+col], veri[4*row+col]], temp2 )                
                if len(ls) == 6:
                    print('bug')
                    #constr += self.genFromConstraintTemplate(self, ls, [oput[4*row+col], fix[4*row+col], veri[4*row+col]], temp3 )    
                if len(ls) == 2:
                    constr.append("%s - %s >= 0" %(ls[0], oput[4*row+col]))
                    constr.append("%s - %s <= 0" %(ls[0], oput[4*row+col]))
                    constr += self.genFromConstraintTemplate(self, ls, [ fix[4*row+col], veri[4*row+col]], temp1 ) 
        return constr
                        
    def previousTKpattern(self, tk): # tk is a vector of 0/1, 1 means active, with fixed diffrence
        return self.perm(tk, self.PTI)          
 
    def nextTKpattern(self, tk): # tk is a vector of 0/1, 1 means active, with fixed diffrence
        return self.perm(tk, self.PT)          
    
    def diffPropagation(self):
        """
        s_i-1 -> ART -> SR,MC -> s_i
        """
        constr = []
        stk = self.previousTKpattern(self.DK1)
        beforeMC = []
        beforeSR = []
        beforeATK = [0 for i in range(self.nCell)]
        
        # for E_b, f-variables always stand for the fixness of difference after S-box 
        for r in [self.lb-1]:
            beforeMC = self.MixColumnInv(self.din)  # din is the exact difference
            beforeSR = self.SRinv(beforeMC)
            for i in range(self.nCell):
                if beforeSR[i]: 
                    beforeSR[i] = 1  # take the active pattern
                ASi = beforeSR[i]
                if i < 8:
                    ASi |= stk[i]  # the effect of injecting stk difference
                beforeATK[i] = ASi
                constr.append(self.assign(self.Diff[r][i], ASi))
                constr.append(self.assign(self.Fix[r][i], 1)) # each byte difference is known and fixed for this round

        for r in range(self.lb-2, 0, -1):
            beforeMC = self.activePatternMCinv(beforeATK)
            print(beforeMC)
            beforeSR = self.SRinv(beforeMC)    
            stk = self.previousTKpattern(stk)
            for i in range(self.nCell):
                ASi = beforeSR[i]
                constr.append(self.assign(self.DiffATK[r][i], ASi))  
                if i < 8 and stk[i] == 1 and ASi ==0: # the byte is passive before injecting stk difference
                    ASi = 1
                    constr.append(self.assign(self.Fix[r][i], 1))    
                else:
                    constr.append(self.assign(self.Fix[r][i], 1^ASi))  # the differnce of passive bytes is also fixed
                constr.append(self.assign(self.Diff[r][i], ASi))                    
                beforeATK[i] = ASi

        print('')
        stk = self.DK2
        for i in range(self.ld):
            stk = self.nextTKpattern(stk)
        afterMC = []
        afterSR = []
        afterATK = [None for i in range(self.nCell)]
        
        for r in [self.lb]:
            afterMC = self.dout  # dout is the exact difference       
            for i in range(self.nCell):
                if afterMC[i]: 
                    afterMC[i] = 1
                ASi = afterMC[i]
                constr.append(self.assign(self.Diff[r][i], ASi))
                constr.append(self.assign(self.Fix[r][i], 1))   # difference of every byte before the first  S-box layer of E_f is fixed     
        
        for r in range(self.lb+1, self.lb + self.lf):
            for i in range(self.nCell):
                ASi = afterMC[i]
                # from the second round of E_f, f-variables denote if the byte after ATK (of the previous round) is fixed or not
                if i < 8 and stk[i] == 1 and ASi ==0:
                    ASi = 1
                    constr.append(self.assign(self.Fix[r][i], 1))    
                else:
                    constr.append(self.assign(self.Fix[r][i], 1^ASi))  
                afterATK[i] = ASi
                constr.append(self.assign(self.DiffATK[r][i], ASi))   
            stk = self.nextTKpattern(stk)
            afterSR = self.SR(afterATK)
            afterMC = self.activePatternMC(afterSR)
            print(afterMC)
            for i in range(self.nCell):
                ASi = afterMC[i]
                constr.append(self.assign(self.Diff[r][i], ASi))   
        # the linear layer of the last round is omitted   
        return constr
 
    def verificationPath(self):
        """
        s_i-1 -> ART -> SR,MC -> s_i
        """
        constr = []
        stk = self.previousTKpattern(self.DK1)
        activebeforeMC = []
        activebeforeMC = []
        activebeforeATK = [0 for i in range(self.nCell)]
        UK = 0
        
        # for E_b
        print('')
        for r in [self.lb-1]:
            activebeforeMC = self.MixColumnInv(self.din)  # din is the exact difference
            activebeforeSR = self.SRinv(activebeforeMC)
            for i in range(self.nCell):
                if activebeforeSR[i]: 
                    activebeforeSR[i] = 1  # take the active pattern
                ASi = activebeforeSR[i]
                if i < 8:
                    ASi |= stk[i]  # the effect of injecting stk difference
                activebeforeATK[i] = ASi
                constr.append(self.assign(self.Value[r][i], ASi)) # the value before the S-box is needed if the S-box is active

        valuebeforeSB = [activebeforeATK[i] for i in range(self.nCell)]
        valuebeforeSR = []
        valuebeforeMC = []
        for r in range(self.lb-2, 0, -1):
            # the first round of E_b is actually omitted
            print('beforeSB', valuebeforeSB)
            valuebeforeMC = self.valuePatternMC(valuebeforeSB)      
            
            activebeforeMC = self.activePatternMCinv(activebeforeATK)
            activebeforeSR = self.SRinv(activebeforeMC)
            valuebeforeSR = self.SRinv(valuebeforeMC)
            print('beforeSR', valuebeforeSR)
            stk = self.previousTKpattern(stk)
            print('STK     ', stk)
            for i in range(self.nCell):
                VSi = valuebeforeSR[i]
                if i < 8 and VSi == 1: # the stk byte is needed
                    constr.append(self.assign(self.UsedKey[r][i], 1))    
                    UK += 1
                else:
                    constr.append(self.assign(self.UsedKey[r][i], 0))  
                ASi = activebeforeSR[i]
                if i < 8 and stk[i] == 1 and ASi ==0: # the byte is passive before injecting stk difference
                    ASi = 1                 
                activebeforeATK[i] = ASi
                if ASi or VSi:
                    valuebeforeSB[i] = 1                
                else:
                    valuebeforeSB[i] = 0
                constr.append(self.assign(self.Value[r][i], valuebeforeSB[i])) 
        print('UK', UK)
        # the first round, acts as the whitening key
        for i in range(self.nCell):       
            if valuebeforeSB[i] == 1:
                constr.append(self.assign(self.UK0[i], 1))    
                UK += 1
            else:
                constr.append(self.assign(self.UK0[i], 0)) 
        print('UK', UK)
        # for E_f
        stk = self.DK2
        for i in range(self.ld):
            stk = self.nextTKpattern(stk)
        activeafterMC = []
        activeafterSR = []
        activeafterATK = [None for i in range(self.nCell)]
        
        for r in [self.lb]:
            # SB, ATK of the first round of E_f
            activeafterMC = self.dout  # dout is the exact difference       
            for i in range(self.nCell):
                if activeafterMC[i]: 
                    activeafterMC[i] = 1
                ASi = activeafterMC[i]
                constr.append(self.assign(self.Value[r][i], ASi))   # value of the output of the Sbox is needed  
                if i < 8:
                    constr.append(self.assign(self.UsedKey[r][i], ASi)) 
                    UK += ASi
                else:
                    constr.append(self.assign(self.UsedKey[r][i], 0)) 
                if i < 8 and stk[i] == 1 and ASi ==0:
                    ASi = 1 
                activeafterATK[i] = ASi
                
        valueafterSB = [activeafterMC[i] for i in range(self.nCell)]
        valueafterSR = []
        valueafterMC = []
        print('')
        for r in range(self.lb+1, self.lb + self.lf):
            # SR, MC of the previous round and SB, ATK of the current round
            print('afterSB', valueafterSB)
            activeafterSR = self.SR(activeafterATK)
            activeafterMC = self.activePatternMC(activeafterSR)
            valueafterSR = self.SR(valueafterSB)
            valueafterMC = self.valuePatternMCinv(valueafterSR)
            print('afterMC', valueafterMC)
            stk = self.nextTKpattern(stk)
            print('STK     ', stk)
            for i in range(self.nCell):
                if valueafterMC[i] or activeafterMC[i]:
                    valueafterSB[i] = 1
                else:
                    valueafterSB[i] = 0
                constr.append(self.assign(self.Value[r][i], valueafterSB[i]))   
                if i < 8:
                    constr.append(self.assign(self.UsedKey[r][i], valueafterSB[i])) 
                    UK += valueafterSB[i]
                else:
                    constr.append(self.assign(self.UsedKey[r][i], 0)) 
                ASi = activeafterMC[i]
                if i < 8 and stk[i] == 1 and ASi == 0:
                    ASi = 1 
                activeafterATK[i] = ASi   
        print(valueafterSB)                                 
        # the linear layer of the last round is omitted   
        print('UK', UK)
        return constr                                                        

    def keyBridge(self, roundkeys, lanesum16, real16, etk0, name):
        """
        16 lanes, each for (ld-1) + lf stk bytes of the same position
        etk0: [0,1,2,3, 0,1,2,3, 7,4,5,6, 0,1,2,3]
        tk0 : [0,1,2,3, 4,5,6,7, 0,0,0,0, 0,0,0,0]
        """
        constr = []
        etk_index = [0,1,2,3, 0,1,2,3, 7,4,5,6, 0,1,2,3]
        for i in range(4):
            constr.append("%s - %s = 0" %(roundkeys[0][etk_index[8+i]], etk0[8+i]))
        for col in range(4):
            ls = []
            for i in [0,1,3]:
                ls.append(etk0[4*i + col])
                constr.append("%s - %s >= 0" %(roundkeys[0][col], etk0[4*i + col]) )
            constr.append("%s - %s >= 0" %(' + '.join(ls) , roundkeys[0][col] ) )
        for i in range(8, self.nCell):
            constr.append(self.assign(roundkeys[0][i], 0)) 
            
        LANES = [ [] for i in range(self.nCell) ]
        tk_index = [i for i in range(self.nCell)]
        for r in range(self.lb-1):
            print(tk_index)
            for i in range(8):
                LANES[tk_index[i]].append( roundkeys[r][i] )
            tk_index = self.nextTKpattern(tk_index)
        for r in range(self.lb-1, self.lb + self.ld):
            tk_index = self.nextTKpattern(tk_index)
        for r in range(self.lb, self.lb + self.lf):
            print(tk_index)
            for i in range(8):
                LANES[tk_index[i]].append( roundkeys[r][i] )
            tk_index = self.nextTKpattern(tk_index)

        for i in range(self.nCell):
            constr.append("%s - %s = 0" %(' + '.join(LANES[i]), lanesum16[i] ))
        
        bigM = 100
        A = ['A'+name+str(i) for i in range(self.nCell)]
        # If lanesum16[i] > z, Ai = 1, to mark if the same byte is guessed more than z times
        # A is binary
        #  z >= sum - bigM*A          =>   sum - bigM A <= z
        #  sum >= z + 1 - bigM*(1-A)  =>   sum - bigM A >= z + 1 - bigM   
        for i in range(self.nCell):
            constr.append("%s - %d %s <= %d" %(lanesum16[i], bigM, A[i], self.z ))
            constr.append("%s - %d %s >= %d" %(lanesum16[i], bigM, A[i], self.z + 1 -bigM ))
        
        # real16[i] = z, if A[i] = 1, else real16[i] = lanesum16[i]
        # sum <= real + bigM*A       => real - sum + bigM A >= 0
        # z   <= real + bigM*(1-A)   => real       - bigM A >= z - bigM
        # real<= z                   => real <= z
        for i in range(self.nCell):
            constr.append("%s - %s + %d %s >= 0" % (real16[i], lanesum16[i], bigM, A[i]) )
            constr.append("%s - %d %s >= %d" % (real16[i], bigM, A[i], self.z-bigM) )
            constr.append("%s <= %d" % (real16[i], self.z) )
        
        return constr
            

    def guessAndDetermine(self):
        """
        di uk gk do       
        0  0  0  0        
        0  1  0  0       
        1  0  0  0        
        1  1  0  0       
        1  1  1  1
        di - gk >= 0
        uk - gk >= 0
        do - gk = 0
        d active f v        d active f v
        1  1     1 1        1  1     1 1
        0  1     1 0        0  1     1 0
        *  0     1 *        *  0     1 0
        *  1     0 0        *  1     0 0
        the constraint from tmp and conditionMC together define v
        v may be 1 when (active,f) = (1,1), (0,1), tmp only captures the former case
        """
        tmp = [(0, 0, 1, -1, 0), (0, 1, 1, 0, -1), (1, -1, 0, -1, 1), (-1, -1, -1, 1, 2) ]
        tmp2 = [(0, 1, 1, -1, -1),(1, 0, 0, -1, 0),(-1, -1, -1, 1, 2)]
        constr = []
        
        # guess-and-determine for the first round
        # (1, 0, -1, 0)  (0, 1, -1, 0)
        for r in [0]: 
            for i in range(self.nCell):
                constr.append(self.assign(self.Dtm_z[r][i], 1)) # plaintext is known
                constr.append("%s - %s >= 0" % (self.Dtm_z[r][i], self.GK0[i]))
                constr.append("%s - %s >= 0" % (self.UK0[i], self.GK0[i]))
                constr.append("%s - %s = 0" % (self.Dtm_x[r+1][i], self.GK0[i]))  
                constr += self.genFromConstraintTemplate(self, [self.Dtm_x[r+1][i], self.Diff[r+1][i], self.Fix[r+1][i]], [self.Verif[r+1][i]], tmp2 )                
       
 
        for r in range(1, self.lb - 1): # each round: ATK, SR, MC, SB
            # ATK: dx uk gk dy
            for i in range(8):
                constr.append("%s - %s >= 0" % (self.Dtm_x[r][i], self.Dtm_y[r][i]))
                constr.append("%s - %s >= 0" % (self.UsedKey[r][i], self.GuessedKey[r][i]))
                constr.append("%s - %s = 0" % (self.Dtm_y[r][i], self.GuessedKey[r][i]))  
            for i in range(8, 16):
                constr.append("%s - %s = 0" % (self.Dtm_y[r][i], self.Dtm_x[r][i]))  
                
            # MC: dy = 1, value is determined
            constr += self.constrValueMCorInv(self.SR(self.Dtm_y[r]), self.Dtm_z[r], self.M)
             
            # check the conditions for MC
            #constr += self.constrConditionMCorInv(self.SR(self.DiffATK[r]), self.Diff[r+1], self.SR(self.Dtm_x[r]), self.Fix[r+1], self.Verif[r+1], self.M)
            constr += self.constrConditionMC(self.SR(self.DiffATK[r]), self.Diff[r+1], self.SR(self.Dtm_x[r]), self.Dtm_z[r], self.Fix[r+1], self.Verif[r+1])
            # SB
            for i in range(self.nCell):
                constr.append("%s - %s = 0" % (self.Dtm_z[r][i], self.Dtm_x[r+1][i]))   
                # E_b uses tmp in order to be compatible with constrs from MC
                constr += self.genFromConstraintTemplate(self, [self.Dtm_x[r+1][i], self.Diff[r+1][i], self.Fix[r+1][i]], [self.Verif[r+1][i]], tmp )                
          
        for r in [self.lb + self.lf - 1]: # ciphertext is known
            for i in range(self.nCell):
                constr.append(self.assign(self.Dtm_y[r][i], 1))   
        for r in [self.lb ]: 
            # ATK: dy uk gk dx
            for i in range(8):
                constr.append("%s - %s >= 0" % (self.Dtm_y[r][i], self.Dtm_x[r][i]))
                constr.append("%s - %s >= 0" % (self.UsedKey[r][i], self.GuessedKey[r][i]))
                constr.append("%s - %s = 0" % (self.Dtm_x[r][i], self.GuessedKey[r][i]))  
            for i in range(8, 16):
                constr.append("%s - %s = 0" % (self.Dtm_y[r][i], self.Dtm_x[r][i]))    
            for i in range(self.nCell):
                # E_f uses tmp2, the exact one since no MC before this SB
                constr += self.genFromConstraintTemplate(self, [self.Dtm_x[r][i], self.Diff[r][i], self.Fix[r][i]], [self.Verif[r][i]], tmp2 )                
                           
        for r in range(self.lb + self.lf-1, self.lb, -1): # each round:  ATK, SB, MCinv, SRinv
            # ATK: dy uk gk dx
            print("Round %d" %(r+self.ld))
            for i in range(8):
                constr.append("%s - %s >= 0" % (self.Dtm_y[r][i], self.Dtm_x[r][i]))
                constr.append("%s - %s >= 0" % (self.UsedKey[r][i], self.GuessedKey[r][i]))
                constr.append("%s - %s = 0" % (self.Dtm_x[r][i], self.GuessedKey[r][i]))  
            for i in range(8, 16):
                constr.append("%s - %s = 0" % (self.Dtm_y[r][i], self.Dtm_x[r][i]))    
            # SB
            for i in range(self.nCell):
                constr.append("%s - %s = 0" % (self.Dtm_x[r][i], self.Dtm_z[r-1][i]))  
               
            # MCinv   
            constr += self.constrValueMCorInv(self.Dtm_z[r-1], self.SR(self.Dtm_y[r-1]), self.Minv)
            #"""             
            # check the conditions for MC, note Fix is defined after ATK for Ef
            #constr += self.constrConditionMCorInv(self.Diff[r], self.SR(self.DiffATK[r]), self.Dtm_z[r-1], self.SR(self.Fix[r]), self.Verif[r], self.Minv)
            constr += self.constrConditionMCinv(self.Diff[r], self.SR(self.DiffATK[r]), self.Dtm_z[r-1], self.SR(self.Dtm_y[r-1]), self.SR(self.Fix[r]), self.Verif[r])

            #"""               
            
        return constr
    
    def defineComplexity(self):        
        constr = []
        list_rb = self.Diff[1]        
        list_rf = self.Diff[self.lb + self.lf-1]            
        list_gk = self.GKreal16
        
        list_vb = []
        for r in range(1, self.lb ):
            list_vb += self.Verif[r]

        list_vf = []
        for r in range(self.lb, self.lb + self.lf):
            list_vf += self.Verif[r] 
            
        mcoef = ' - ' + str(self.cell) + ' '
        pcoef = ' + ' + str(self.cell) + ' '
        mcoef2 = ' - ' + str(self.cell*2) + ' '
        pcoef2 = ' + ' + str(self.cell*2) + ' '
        
        minus_gk = " - %d %s" % (self.cell, mcoef.join(list_gk) )
        constr.append("%s%s >= %s" %(self.TV[1], minus_gk, str(int(round(self.D+2)))))
        
        rbp = " + %d %s" % (self.cell, pcoef.join(list_vb) )
        rfp = " + %d %s" % (self.cell, pcoef.join(list_vf) )
        rfp2 = " + %d %s" % (self.cell*2, pcoef2.join(list_vf) )       
        rbp2 = " + %d %s" % (self.cell*2, pcoef2.join(list_vb) ) 
        minus_rf = " - %d %s" % (self.cell, mcoef.join(list_rf) )   
        minus_rb = " - %d %s" % (self.cell, mcoef.join(list_rb) )   
        minus_rf2 = " - %d %s" % (self.cell*2, mcoef2.join(list_rf) )   
        minus_rb2 = " - %d %s" % (self.cell*2, mcoef2.join(list_rb) )  
        if self.isB == 1:
            minus_T2 = minus_gk  + minus_rb + rbp 
            constr.append("%s%s >= %d" %(self.TV[2], minus_T2, int(round(self.D  ))))
        else:
            minus_T2 = minus_gk  + minus_rf + rfp  
            constr.append("%s%s >= %d" %(self.TV[2], minus_T2, int(round(self.D*2-self.n  ))))
        minus_T3 = minus_gk + minus_rb2 + minus_rf2 + rbp2 + rfp2
        constr.append("%s%s >= %d" %(self.TV[3], minus_T3, int(round(self.D*2 - 2*self.n ))))
        print(int(round(self.D*2 - 2*self.n - 2)))
        constr.append("%s - %s >= 0" %(self.TV[0], self.TV[1]))
        constr.append("%s - %s >= 0" %(self.TV[0], self.TV[2]))  
        constr.append("%s - %s >= 0" %(self.TV[0], self.TV[3]))
        return constr
    
    def genObj(self):
        return self.TV[0]

    
    def readSol(self, filename):
        solFile = open(filename,'r')
        var_value_map = dict()
        for line in solFile:
            if line[0] != '#':
                temp = line
                temp = temp.split()
                var_value_map[temp[0]] = int(round(float(temp[1]))) 
                
        list_rb = self.Diff[1]        
        list_rf = self.Diff[self.lb + self.lf-1]            
        list_gk = self.GKreal16
        list_uk = self.UKreal16       
        list_vb = []
        for r in range(1, self.lb ):
            list_vb += self.Verif[r]

        list_vf = []
        for r in range(self.lb, self.lb + self.lf):
            list_vf += self.Verif[r] 

        rb = 0
        for v in list_rb:
            rb += var_value_map[v]
        print("rb = %d" %rb)
        rf = 0
        for v in list_rf:
            rf += var_value_map[v]
        print("rf = %d" %rf)
        
        gk = 0
        for v in list_gk:
            gk += var_value_map[v]
        print("gk = %d" %gk)  
        
        uk = 0
        for v in list_uk:
            uk += var_value_map[v]
        print("uk = %d" %uk)
        
        listUK = []
        for r in range(self.lb-1):
            listUK += self.UsedKey[r]
        for r in  range(self.lb, self.lb+self.lf):
            listUK += self.UsedKey[r]

            
        UK = 0
        for v in listUK:
            UK += var_value_map[v]
        print("UK = %d" %UK)
        
        listGK = []
        for r in range(self.lb-1):
            listGK += self.GuessedKey[r]
        for r in range(self.lb, self.lb + self.lf):
            listGK += self.GuessedKey[r]
        for v in listGK:
            if v in var_value_map:
                if var_value_map[v]:
                    print(v)
                    
                    
        list_vb = []
        for r in range(1, self.lb ):
            list_vb += self.Verif[r]
        vb = 0
        for v in list_vb:
            num = var_value_map[v]
            vb += num
            if num:
                print(v)
        print("vb = %d" %vb)
        list_vf = []
        for r in range(self.lb, self.lb + self.lf):
            list_vf += self.Verif[r]        
        vf = 0
        for v in list_vf:
            num = var_value_map[v]
            vf += num
            if num:
                print(v)
        print("vf = %d" %vf)
        
        # for r in range(1, self.lb-1):
        #     print("round %d dx"%r)
        #     for i in range(16):
        #         print(var_value_map[self.Dtm_x[r][i]])
        #     print("round %d dy"%r)
        #     for i in range(16):
        #         print(var_value_map[self.Dtm_y[r][i]])
                
    def returnGeneralVset(self):
        V = []
        V += self.UKreal16 
        V += self.UKlaneSum16 
        V += self.GKreal16 
        V += self.GKlaneSum16
        V += self.TV        
        return set(V)

        
    def genModel(self):
        C = list([])
        C += self.diffPropagation()
        C += self.verificationPath()
        C += self.keyBridge(self.UsedKey, self.UKlaneSum16, self.UKreal16, self.UK0, 'u')
        C += self.keyBridge(self.GuessedKey, self.GKlaneSum16, self.GKreal16, self.GK0, 'g')
        C += self.guessAndDetermine()
        C += self.defineComplexity()

        V = self.getVariables_From_Constraints(self, C)
        
        GV = self.returnGeneralVset()
        BV = V - GV
        obj = self.genObj()

        name = 'skinny'
        self.writeFile(name + '.lp', obj, C, BV, GV)
        m = read(name + '.lp')
        m.optimize()
        # m.computeIIS()
        # m.write("skinny.ilp")
        
        m.write(name+'.sol')
        self.readSol(name+'.sol')              


if __name__ == '__main__':
    print("hello world")
    
    #serpent = SERPENT(58.15, 1, 8, 1)
    serpent = SERPENT(60.3, 1, 8, 1)
    serpent.genModel()
    
    isB = 1
    #skinny = SKINNY(64, 3, 28.78, 4, 22, 5, isB)    
    #skinny = SKINNY(128, 3, 57.55, 4, 23, 5, isB)
    skinny = SKINNY( 64, 2, 27.67, 3, 18, 4, isB)
    #skinny = SKINNY(128, 2, 54.26, 4, 18, 3, isB) # attack 25 rounds
    #skinny = SKINNY(128, 2, 60.54, 3, 19, 4, isB) # attack 26 rounds

    skinny.genModel()
