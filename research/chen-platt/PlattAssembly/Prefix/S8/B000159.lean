import PlattAssemblyKernel
import PlattCertificates.Count131072.C075088
import PlattCertificates.Count131072.C075089
import PlattCertificates.Count131072.C075090
import PlattCertificates.Count131072.C075091
import PlattCertificates.Count131072.C075092
import PlattCertificates.Count131072.C075093
import PlattCertificates.Count131072.C075094
import PlattCertificates.Count131072.C075095
import PlattCertificates.Count131072.C075096
import PlattCertificates.Count131072.C075097
import PlattCertificates.Count131072.C075098
import PlattCertificates.Count131072.C075099
import PlattCertificates.Count131072.C075100
import PlattCertificates.Count131072.C075101
import PlattCertificates.Count131072.C075102
import PlattCertificates.Count131072.C075103
import PlattCertificates.Count131072.C075104
import PlattCertificates.Count131072.C075105
import PlattCertificates.Count131072.C075106
import PlattCertificates.Count131072.C075107
import PlattCertificates.Count131072.C075108
import PlattCertificates.Count131072.C075109
import PlattCertificates.Count131072.C075110
import PlattCertificates.Count131072.C075111
import PlattCertificates.Count131072.C075112
import PlattCertificates.Count131072.C075113
import PlattCertificates.Count131072.C075114
import PlattCertificates.Count131072.C075115
import PlattCertificates.Count131072.C075116
import PlattCertificates.Count131072.C075117
import PlattCertificates.Count131072.C075118
import PlattCertificates.Count131072.C075119
namespace ChenEffective.PlattWindow.Assembly.Prefix.S8.B000159
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts75088 : List PrefixCut := [⟨29,74128790,74128833⟩,
⟨64,161178797,161178893⟩]
theorem checked75088 : checkPrefixCuts (2^48) 9845866497 10 Manual.Count131072.C075088.packed 64 cuts75088 = true := by
 decide +kernel
def pointBounds75088 : List (Nat × Nat × Nat) := [(9845925888,116673135582974,116673525598969)]
theorem point_links_checked75088 : (cuts75088.take 1).map (fun c => (9845866497-1+2*2^10*c.k,116673061454184+c.lower,116673451470136+c.upper)) = pointBounds75088 := by
 decide +kernel
def cuts75089 : List PrefixCut := [⟨64,161176650,161176744⟩]
theorem checked75089 : checkPrefixCuts (2^48) 9845997569 10 Manual.Count131072.C075089.packed 64 cuts75089 = true := by
 decide +kernel
def cuts75090 : List PrefixCut := [⟨52,134560011,134560093⟩,
⟨64,164604972,164605071⟩]
theorem checked75090 : checkPrefixCuts (2^48) 9846128641 10 Manual.Count131072.C075090.packed 64 cuts75090 = true := by
 decide +kernel
def pointBounds75090 : List (Nat × Nat × Nat) := [(9846235136,116673518369642,116673908385866)]
theorem point_links_checked75090 : (cuts75090.take 1).map (fun c => (9846128641-1+2*2^10*c.k,116673383809631+c.lower,116673773825773+c.upper)) = pointBounds75090 := by
 decide +kernel
def cuts75091 : List PrefixCut := [⟨64,162487347,162487447⟩]
theorem checked75091 : checkPrefixCuts (2^48) 9846259713 10 Manual.Count131072.C075091.packed 64 cuts75091 = true := by
 decide +kernel
def cuts75092 : List PrefixCut := [⟨64,163742992,163743089⟩]
theorem checked75092 : checkPrefixCuts (2^48) 9846390785 10 Manual.Count131072.C075092.packed 64 cuts75092 = true := by
 decide +kernel
def cuts75093 : List PrefixCut := [⟨11,28157400,28157416⟩,
⟨64,161711207,161711307⟩]
theorem checked75093 : checkPrefixCuts (2^48) 9846521857 10 Manual.Count131072.C075093.packed 64 cuts75093 = true := by
 decide +kernel
def pointBounds75093 : List (Nat × Nat × Nat) := [(9846544384,116673902802342,116674292818796)]
theorem point_links_checked75093 : (cuts75093.take 1).map (fun c => (9846521857-1+2*2^10*c.k,116673874644942+c.lower,116674264661380+c.upper)) = pointBounds75093 := by
 decide +kernel
def cuts75094 : List PrefixCut := [⟨64,161480359,161480459⟩]
theorem checked75094 : checkPrefixCuts (2^48) 9846652929 10 Manual.Count131072.C075094.packed 64 cuts75094 = true := by
 decide +kernel
def cuts75095 : List PrefixCut := [⟨34,87585552,87585601⟩,
⟨64,163822204,163822299⟩]
theorem checked75095 : checkPrefixCuts (2^48) 9846784001 10 Manual.Count131072.C075095.packed 64 cuts75095 = true := by
 decide +kernel
def pointBounds75095 : List (Nat × Nat × Nat) := [(9846853632,116674285422060,116674675438747)]
theorem point_links_checked75095 : (cuts75095.take 1).map (fun c => (9846784001-1+2*2^10*c.k,116674197836508+c.lower,116674587853146+c.upper)) = pointBounds75095 := by
 decide +kernel
def cuts75096 : List PrefixCut := [⟨64,162876722,162876818⟩]
theorem checked75096 : checkPrefixCuts (2^48) 9846915073 10 Manual.Count131072.C075096.packed 64 cuts75096 = true := by
 decide +kernel
def cuts75097 : List PrefixCut := [⟨57,147181764,147181848⟩,
⟨64,164646798,164646893⟩]
theorem checked75097 : checkPrefixCuts (2^48) 9847046145 10 Manual.Count131072.C075097.packed 64 cuts75097 = true := by
 decide +kernel
def pointBounds75097 : List (Nat × Nat × Nat) := [(9847162880,116674671717198,116675061734111)]
theorem point_links_checked75097 : (cuts75097.take 1).map (fun c => (9847046145-1+2*2^10*c.k,116674524535434+c.lower,116674914552263+c.upper)) = pointBounds75097 := by
 decide +kernel
def cuts75098 : List PrefixCut := [⟨64,161214518,161214611⟩]
theorem checked75098 : checkPrefixCuts (2^48) 9847177217 10 Manual.Count131072.C075098.packed 64 cuts75098 = true := by
 decide +kernel
def cuts75099 : List PrefixCut := [⟨64,161212364,161212460⟩]
theorem checked75099 : checkPrefixCuts (2^48) 9847308289 10 Manual.Count131072.C075099.packed 64 cuts75099 = true := by
 decide +kernel
def cuts75100 : List PrefixCut := [⟨16,39731084,39731107⟩,
⟨64,163068128,163068227⟩]
theorem checked75100 : checkPrefixCuts (2^48) 9847439361 10 Manual.Count131072.C075100.packed 64 cuts75100 = true := by
 decide +kernel
def pointBounds75100 : List (Nat × Nat × Nat) := [(9847472128,116675051340198,116675441357334)]
theorem point_links_checked75100 : (cuts75100.take 1).map (fun c => (9847439361-1+2*2^10*c.k,116675011609114+c.lower,116675401626227+c.upper)) = pointBounds75100 := by
 decide +kernel
def cuts75101 : List PrefixCut := [⟨64,161894072,161894172⟩]
theorem checked75101 : checkPrefixCuts (2^48) 9847570433 10 Manual.Count131072.C075101.packed 64 cuts75101 = true := by
 decide +kernel
def cuts75102 : List PrefixCut := [⟨39,98810343,98810403⟩,
⟨64,163521114,163521212⟩]
theorem checked75102 : checkPrefixCuts (2^48) 9847701505 10 Manual.Count131072.C075102.packed 64 cuts75102 = true := by
 decide +kernel
def pointBounds75102 : List (Nat × Nat × Nat) := [(9847781376,116675435381657,116675825399029)]
theorem point_links_checked75102 : (cuts75102.take 1).map (fun c => (9847701505-1+2*2^10*c.k,116675336571314+c.lower,116675726588626+c.upper)) = pointBounds75102 := by
 decide +kernel
def cuts75103 : List PrefixCut := [⟨64,161661089,161661186⟩]
theorem checked75103 : checkPrefixCuts (2^48) 9847832577 10 Manual.Count131072.C075103.packed 64 cuts75103 = true := by
 decide +kernel
def cuts75104 : List PrefixCut := [⟨62,157171625,157171722⟩,
⟨64,162116253,162116353⟩]
theorem checked75104 : checkPrefixCuts (2^48) 9847963649 10 Manual.Count131072.C075104.packed 64 cuts75104 = true := by
 decide +kernel
def pointBounds75104 : List (Nat × Nat × Nat) := [(9848090624,116675818925142,116676208942746)]
theorem point_links_checked75104 : (cuts75104.take 1).map (fun c => (9847963649-1+2*2^10*c.k,116675661753517+c.lower,116676051771024+c.upper)) = pointBounds75104 := by
 decide +kernel
def cuts75105 : List PrefixCut := [⟨64,163628916,163629011⟩]
theorem checked75105 : checkPrefixCuts (2^48) 9848094721 10 Manual.Count131072.C075105.packed 64 cuts75105 = true := by
 decide +kernel
def cuts75106 : List PrefixCut := [⟨64,161740381,161740477⟩]
theorem checked75106 : checkPrefixCuts (2^48) 9848225793 10 Manual.Count131072.C075106.packed 64 cuts75106 = true := by
 decide +kernel
def cuts75107 : List PrefixCut := [⟨21,54475078,54475104⟩,
⟨64,165853853,165853946⟩]
theorem checked75107 : checkPrefixCuts (2^48) 9848356865 10 Manual.Count131072.C075107.packed 64 cuts75107 = true := by
 decide +kernel
def pointBounds75107 : List (Nat × Nat × Nat) := [(9848399872,116676203714145,116676593731969)]
theorem point_links_checked75107 : (cuts75107.take 1).map (fun c => (9848356865-1+2*2^10*c.k,116676149239067+c.lower,116676539256865+c.upper)) = pointBounds75107 := by
 decide +kernel
def cuts75108 : List PrefixCut := [⟨64,162221941,162222037⟩]
theorem checked75108 : checkPrefixCuts (2^48) 9848487937 10 Manual.Count131072.C075108.packed 64 cuts75108 = true := by
 decide +kernel
def cuts75109 : List PrefixCut := [⟨44,112290850,112290919⟩,
⟨64,162362691,162362790⟩]
theorem checked75109 : checkPrefixCuts (2^48) 9848619009 10 Manual.Count131072.C075109.packed 64 cuts75109 = true := by
 decide +kernel
def pointBounds75109 : List (Nat × Nat × Nat) := [(9848709120,116676589605711,116676979623767)]
theorem point_links_checked75109 : (cuts75109.take 1).map (fun c => (9848619009-1+2*2^10*c.k,116676477314861+c.lower,116676867332848+c.upper)) = pointBounds75109 := by
 decide +kernel
def cuts75110 : List PrefixCut := [⟨64,164589730,164589823⟩]
theorem checked75110 : checkPrefixCuts (2^48) 9848750081 10 Manual.Count131072.C075110.packed 64 cuts75110 = true := by
 decide +kernel
def cuts75111 : List PrefixCut := [⟨64,162072566,162072666⟩]
theorem checked75111 : checkPrefixCuts (2^48) 9848881153 10 Manual.Count131072.C075111.packed 64 cuts75111 = true := by
 decide +kernel
def cuts75112 : List PrefixCut := [⟨3,7916380,7916384⟩,
⟨64,161956094,161956190⟩]
theorem checked75112 : checkPrefixCuts (2^48) 9849012225 10 Manual.Count131072.C075112.packed 64 cuts75112 = true := by
 decide +kernel
def pointBounds75112 : List (Nat × Nat × Nat) := [(9849018368,116676974256228,116677364274511)]
theorem point_links_checked75112 : (cuts75112.take 1).map (fun c => (9849012225-1+2*2^10*c.k,116676966339848+c.lower,116677356358127+c.upper)) = pointBounds75112 := by
 decide +kernel
def cuts75113 : List PrefixCut := [⟨64,163954434,163954533⟩]
theorem checked75113 : checkPrefixCuts (2^48) 9849143297 10 Manual.Count131072.C075113.packed 64 cuts75113 = true := by
 decide +kernel
def cuts75114 : List PrefixCut := [⟨26,66215592,66215635⟩,
⟨64,163066330,163066430⟩]
theorem checked75114 : checkPrefixCuts (2^48) 9849274369 10 Manual.Count131072.C075114.packed 64 cuts75114 = true := by
 decide +kernel
def pointBounds75114 : List (Nat × Nat × Nat) := [(9849327616,116677358465968,116677748484485)]
theorem point_links_checked75114 : (cuts75114.take 1).map (fun c => (9849274369-1+2*2^10*c.k,116677292250376+c.lower,116677682268850+c.upper)) = pointBounds75114 := by
 decide +kernel
def cuts75115 : List PrefixCut := [⟨64,162692650,162692748⟩]
theorem checked75115 : checkPrefixCuts (2^48) 9849405441 10 Manual.Count131072.C075115.packed 64 cuts75115 = true := by
 decide +kernel
def cuts75116 : List PrefixCut := [⟨49,124111347,124111416⟩,
⟨64,162204675,162204765⟩]
theorem checked75116 : checkPrefixCuts (2^48) 9849536513 10 Manual.Count131072.C075116.packed 64 cuts75116 = true := by
 decide +kernel
def pointBounds75116 : List (Nat × Nat × Nat) := [(9849636864,116677742120703,116678132139444)]
theorem point_links_checked75116 : (cuts75116.take 1).map (fun c => (9849536513-1+2*2^10*c.k,116677618009356+c.lower,116678008028028+c.upper)) = pointBounds75116 := by
 decide +kernel
def cuts75117 : List PrefixCut := [⟨64,161059435,161059534⟩]
theorem checked75117 : checkPrefixCuts (2^48) 9849667585 10 Manual.Count131072.C075117.packed 64 cuts75117 = true := by
 decide +kernel
def cuts75118 : List PrefixCut := [⟨64,161400208,161400310⟩]
theorem checked75118 : checkPrefixCuts (2^48) 9849798657 10 Manual.Count131072.C075118.packed 64 cuts75118 = true := by
 decide +kernel
def cuts75119 : List PrefixCut := [⟨8,20403487,20403499⟩,
⟨64,160883702,160883808⟩]
theorem checked75119 : checkPrefixCuts (2^48) 9849929729 10 Manual.Count131072.C075119.packed 64 cuts75119 = true := by
 decide +kernel
def pointBounds75119 : List (Nat × Nat × Nat) := [(9849946112,116678123077161,116678513096136)]
theorem point_links_checked75119 : (cuts75119.take 1).map (fun c => (9849929729-1+2*2^10*c.k,116678102673674+c.lower,116678492692637+c.upper)) = pointBounds75119 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S8.B000159
