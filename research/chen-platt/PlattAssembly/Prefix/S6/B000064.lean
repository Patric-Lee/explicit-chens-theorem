import PlattAssemblyKernel
import PlattCertificates.Count131072.C052048
import PlattCertificates.Count131072.C052049
import PlattCertificates.Count131072.C052050
import PlattCertificates.Count131072.C052051
import PlattCertificates.Count131072.C052052
import PlattCertificates.Count131072.C052053
import PlattCertificates.Count131072.C052054
import PlattCertificates.Count131072.C052055
import PlattCertificates.Count131072.C052056
import PlattCertificates.Count131072.C052057
import PlattCertificates.Count131072.C052058
import PlattCertificates.Count131072.C052059
import PlattCertificates.Count131072.C052060
import PlattCertificates.Count131072.C052061
import PlattCertificates.Count131072.C052062
import PlattCertificates.Count131072.C052063
import PlattCertificates.Count131072.C052064
import PlattCertificates.Count131072.C052065
import PlattCertificates.Count131072.C052066
import PlattCertificates.Count131072.C052067
import PlattCertificates.Count131072.C052068
import PlattCertificates.Count131072.C052069
import PlattCertificates.Count131072.C052070
import PlattCertificates.Count131072.C052071
import PlattCertificates.Count131072.C052072
import PlattCertificates.Count131072.C052073
import PlattCertificates.Count131072.C052074
import PlattCertificates.Count131072.C052075
import PlattCertificates.Count131072.C052076
import PlattCertificates.Count131072.C052077
import PlattCertificates.Count131072.C052078
import PlattCertificates.Count131072.C052079
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000064
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts52048 : List PrefixCut := [⟨64,238258727,238258860⟩]
theorem checked52048 : checkPrefixCuts (2^48) 6825967617 10 Manual.Count131072.C052048.packed 64 cuts52048 = true := by
 decide +kernel
def cuts52049 : List PrefixCut := [⟨3,11339649,11339656⟩,
⟨64,239821060,239821195⟩]
theorem checked52049 : checkPrefixCuts (2^48) 6826098689 10 Manual.Count131072.C052049.packed 64 cuts52049 = true := by
 decide +kernel
def pointBounds52049 : List (Nat × Nat × Nat) := [(6826104832,112156278736710,112156666142744)]
theorem point_links_checked52049 : (cuts52049.take 1).map (fun c => (6826098689-1+2*2^10*c.k,112156267397061+c.lower,112156654803088+c.upper)) = pointBounds52049 := by
 decide +kernel
def cuts52050 : List PrefixCut := [⟨44,164111484,164111580⟩,
⟨64,238950550,238950688⟩]
theorem checked52050 : checkPrefixCuts (2^48) 6826229761 10 Manual.Count131072.C052050.packed 64 cuts52050 = true := by
 decide +kernel
def pointBounds52050 : List (Nat × Nat × Nat) := [(6826319872,112156671329605,112157058735863)]
theorem point_links_checked52050 : (cuts52050.take 1).map (fun c => (6826229761-1+2*2^10*c.k,112156507218121+c.lower,112156894624283+c.upper)) = pointBounds52050 := by
 decide +kernel
def cuts52051 : List PrefixCut := [⟨64,239069664,239069797⟩]
theorem checked52051 : checkPrefixCuts (2^48) 6826360833 10 Manual.Count131072.C052051.packed 64 cuts52051 = true := by
 decide +kernel
def cuts52052 : List PrefixCut := [⟨21,79578923,79578965⟩,
⟨64,236467456,236467589⟩]
theorem checked52052 : checkPrefixCuts (2^48) 6826491905 10 Manual.Count131072.C052052.packed 64 cuts52052 = true := by
 decide +kernel
def pointBounds52052 : List (Nat × Nat × Nat) := [(6826534912,112157064817258,112157452223733)]
theorem point_links_checked52052 : (cuts52052.take 1).map (fun c => (6826491905-1+2*2^10*c.k,112156985238335+c.lower,112157372644768+c.upper)) = pointBounds52052 := by
 decide +kernel
def cuts52053 : List PrefixCut := [⟨62,228257882,228258014⟩,
⟨64,235267178,235267316⟩]
theorem checked52053 : checkPrefixCuts (2^48) 6826622977 10 Manual.Count131072.C052053.packed 64 cuts52053 = true := by
 decide +kernel
def pointBounds52053 : List (Nat × Nat × Nat) := [(6826749952,112157449963673,112157837370371)]
theorem point_links_checked52053 : (cuts52053.take 1).map (fun c => (6826622977-1+2*2^10*c.k,112157221705791+c.lower,112157609112357+c.upper)) = pointBounds52053 := by
 decide +kernel
def cuts52054 : List PrefixCut := [⟨64,241570968,241571107⟩]
theorem checked52054 : checkPrefixCuts (2^48) 6826754049 10 Manual.Count131072.C052054.packed 64 cuts52054 = true := by
 decide +kernel
def cuts52055 : List PrefixCut := [⟨39,146944115,146944200⟩,
⟨64,240741722,240741859⟩]
theorem checked52055 : checkPrefixCuts (2^48) 6826885121 10 Manual.Count131072.C052055.packed 64 cuts52055 = true := by
 decide +kernel
def pointBounds52055 : List (Nat × Nat × Nat) := [(6826964992,112157845488052,112158232894980)]
theorem point_links_checked52055 : (cuts52055.take 1).map (fun c => (6826885121-1+2*2^10*c.k,112157698543937+c.lower,112158085950780+c.upper)) = pointBounds52055 := by
 decide +kernel
def cuts52056 : List PrefixCut := [⟨64,237397546,237397684⟩]
theorem checked52056 : checkPrefixCuts (2^48) 6827016193 10 Manual.Count131072.C052056.packed 64 cuts52056 = true := by
 decide +kernel
def cuts52057 : List PrefixCut := [⟨16,58132429,58132461⟩,
⟨64,238877198,238877331⟩]
theorem checked52057 : checkPrefixCuts (2^48) 6827147265 10 Manual.Count131072.C052057.packed 64 cuts52057 = true := by
 decide +kernel
def pointBounds52057 : List (Nat × Nat × Nat) := [(6827180032,112158234815634,112158622222784)]
theorem point_links_checked52057 : (cuts52057.take 1).map (fun c => (6827147265-1+2*2^10*c.k,112158176683205+c.lower,112158564090323+c.upper)) = pointBounds52057 := by
 decide +kernel
def cuts52058 : List PrefixCut := [⟨57,214672264,214672384⟩,
⟨64,240068240,240068374⟩]
theorem checked52058 : checkPrefixCuts (2^48) 6827278337 10 Manual.Count131072.C052058.packed 64 cuts52058 = true := by
 decide +kernel
def pointBounds52058 : List (Nat × Nat × Nat) := [(6827395072,112158630232667,112159017640038)]
theorem point_links_checked52058 : (cuts52058.take 1).map (fun c => (6827278337-1+2*2^10*c.k,112158415560403+c.lower,112158802967654+c.upper)) = pointBounds52058 := by
 decide +kernel
def cuts52059 : List PrefixCut := [⟨64,243238066,243238205⟩]
theorem checked52059 : checkPrefixCuts (2^48) 6827409409 10 Manual.Count131072.C052059.packed 64 cuts52059 = true := by
 decide +kernel
def cuts52060 : List PrefixCut := [⟨34,125121464,125121537⟩,
⟨64,238492386,238492523⟩]
theorem checked52060 : checkPrefixCuts (2^48) 6827540481 10 Manual.Count131072.C052060.packed 64 cuts52060 = true := by
 decide +kernel
def pointBounds52060 : List (Nat × Nat × Nat) := [(6827610112,112159023988173,112159411395770)]
theorem point_links_checked52060 : (cuts52060.take 1).map (fun c => (6827540481-1+2*2^10*c.k,112158898866709+c.lower,112159286274233+c.upper)) = pointBounds52060 := by
 decide +kernel
def cuts52061 : List PrefixCut := [⟨64,237828236,237828372⟩]
theorem checked52061 : checkPrefixCuts (2^48) 6827671553 10 Manual.Count131072.C052061.packed 64 cuts52061 = true := by
 decide +kernel
def cuts52062 : List PrefixCut := [⟨11,41719443,41719468⟩,
⟨64,238854273,238854408⟩]
theorem checked52062 : checkPrefixCuts (2^48) 6827802625 10 Manual.Count131072.C052062.packed 64 cuts52062 = true := by
 decide +kernel
def pointBounds52062 : List (Nat × Nat × Nat) := [(6827825152,112159416906774,112159804314596)]
theorem point_links_checked52062 : (cuts52062.take 1).map (fun c => (6827802625-1+2*2^10*c.k,112159375187331+c.lower,112159762595128+c.upper)) = pointBounds52062 := by
 decide +kernel
def cuts52063 : List PrefixCut := [⟨52,194122415,194122524⟩,
⟨64,239715392,239715526⟩]
theorem checked52063 : checkPrefixCuts (2^48) 6827933697 10 Manual.Count131072.C052063.packed 64 cuts52063 = true := by
 decide +kernel
def pointBounds52063 : List (Nat × Nat × Nat) := [(6828040192,112159808164019,112160195572060)]
theorem point_links_checked52063 : (cuts52063.take 1).map (fun c => (6827933697-1+2*2^10*c.k,112159614041604+c.lower,112160001449536+c.upper)) = pointBounds52063 := by
 decide +kernel
def cuts52064 : List PrefixCut := [⟨64,237814545,237814674⟩]
theorem checked52064 : checkPrefixCuts (2^48) 6828064769 10 Manual.Count131072.C052064.packed 64 cuts52064 = true := by
 decide +kernel
def cuts52065 : List PrefixCut := [⟨29,109692437,109692498⟩,
⟨64,240283299,240283433⟩]
theorem checked52065 : checkPrefixCuts (2^48) 6828195841 10 Manual.Count131072.C052065.packed 64 cuts52065 = true := by
 decide +kernel
def pointBounds52065 : List (Nat × Nat × Nat) := [(6828255232,112160201263978,112160588672234)]
theorem point_links_checked52065 : (cuts52065.take 1).map (fun c => (6828195841-1+2*2^10*c.k,112160091571541+c.lower,112160478979736+c.upper)) = pointBounds52065 := by
 decide +kernel
def cuts52066 : List PrefixCut := [⟨64,238629852,238629988⟩]
theorem checked52066 : checkPrefixCuts (2^48) 6828326913 10 Manual.Count131072.C052066.packed 64 cuts52066 = true := by
 decide +kernel
def cuts52067 : List PrefixCut := [⟨6,22424126,22424140⟩,
⟨64,238213059,238213195⟩]
theorem checked52067 : checkPrefixCuts (2^48) 6828457985 10 Manual.Count131072.C052067.packed 64 cuts52067 = true := by
 decide +kernel
def pointBounds52067 : List (Nat × Nat × Nat) := [(6828470272,112160592908818,112160980317297)]
theorem point_links_checked52067 : (cuts52067.take 1).map (fun c => (6828457985-1+2*2^10*c.k,112160570484692+c.lower,112160957893157+c.upper)) = pointBounds52067 := by
 decide +kernel
def cuts52068 : List PrefixCut := [⟨47,175348926,175349029⟩,
⟨64,237507751,237507890⟩]
theorem checked52068 : checkPrefixCuts (2^48) 6828589057 10 Manual.Count131072.C052068.packed 64 cuts52068 = true := by
 decide +kernel
def pointBounds52068 : List (Nat × Nat × Nat) := [(6828685312,112160984046677,112161371455381)]
theorem point_links_checked52068 : (cuts52068.take 1).map (fun c => (6828589057-1+2*2^10*c.k,112160808697751+c.lower,112161196106352+c.upper)) = pointBounds52068 := by
 decide +kernel
def cuts52069 : List PrefixCut := [⟨64,236184163,236184295⟩]
theorem checked52069 : checkPrefixCuts (2^48) 6828720129 10 Manual.Count131072.C052069.packed 64 cuts52069 = true := by
 decide +kernel
def cuts52070 : List PrefixCut := [⟨24,87918712,87918761⟩,
⟨64,238075668,238075800⟩]
theorem checked52070 : checkPrefixCuts (2^48) 6828851201 10 Manual.Count131072.C052070.packed 64 cuts52070 = true := by
 decide +kernel
def pointBounds52070 : List (Nat × Nat × Nat) := [(6828900352,112161370308377,112161757717298)]
theorem point_links_checked52070 : (cuts52070.take 1).map (fun c => (6828851201-1+2*2^10*c.k,112161282389665+c.lower,112161669798537+c.upper)) = pointBounds52070 := by
 decide +kernel
def cuts52071 : List PrefixCut := [⟨64,238936696,238936832⟩]
theorem checked52071 : checkPrefixCuts (2^48) 6828982273 10 Manual.Count131072.C052071.packed 64 cuts52071 = true := by
 decide +kernel
def cuts52072 : List PrefixCut := [⟨1,3544653,3544655⟩,
⟨64,239838842,239838981⟩]
theorem checked52072 : checkPrefixCuts (2^48) 6829113345 10 Manual.Count131072.C052072.packed 64 cuts52072 = true := by
 decide +kernel
def pointBounds52072 : List (Nat × Nat × Nat) := [(6829115392,112161762946682,112162150355824)]
theorem point_links_checked52072 : (cuts52072.take 1).map (fun c => (6829113345-1+2*2^10*c.k,112161759402029+c.lower,112162146811169+c.upper)) = pointBounds52072 := by
 decide +kernel
def cuts52073 : List PrefixCut := [⟨42,157856705,157856793⟩,
⟨64,240905850,240905984⟩]
theorem checked52073 : checkPrefixCuts (2^48) 6829244417 10 Manual.Count131072.C052073.packed 64 cuts52073 = true := by
 decide +kernel
def pointBounds52073 : List (Nat × Nat × Nat) := [(6829330432,112162157097576,112162544506943)]
theorem point_links_checked52073 : (cuts52073.take 1).map (fun c => (6829244417-1+2*2^10*c.k,112161999240871+c.lower,112162386650150+c.upper)) = pointBounds52073 := by
 decide +kernel
def cuts52074 : List PrefixCut := [⟨64,235089938,235090073⟩]
theorem checked52074 : checkPrefixCuts (2^48) 6829375489 10 Manual.Count131072.C052074.packed 64 cuts52074 = true := by
 decide +kernel
def cuts52075 : List PrefixCut := [⟨19,71877932,71877973⟩,
⟨64,240360833,240360970⟩]
theorem checked52075 : checkPrefixCuts (2^48) 6829506561 10 Manual.Count131072.C052075.packed 64 cuts52075 = true := by
 decide +kernel
def pointBounds52075 : List (Nat × Nat × Nat) := [(6829545472,112162547114591,112162934524180)]
theorem point_links_checked52075 : (cuts52075.take 1).map (fun c => (6829506561-1+2*2^10*c.k,112162475236659+c.lower,112162862646207+c.upper)) = pointBounds52075 := by
 decide +kernel
def cuts52076 : List PrefixCut := [⟨60,224200734,224200862⟩,
⟨64,240315006,240315142⟩]
theorem checked52076 : checkPrefixCuts (2^48) 6829637633 10 Manual.Count131072.C052076.packed 64 cuts52076 = true := by
 decide +kernel
def pointBounds52076 : List (Nat × Nat × Nat) := [(6829760512,112162939798226,112163327208039)]
theorem point_links_checked52076 : (cuts52076.take 1).map (fun c => (6829637633-1+2*2^10*c.k,112162715597492+c.lower,112163103007177+c.upper)) = pointBounds52076 := by
 decide +kernel
def cuts52077 : List PrefixCut := [⟨64,238167330,238167470⟩]
theorem checked52077 : checkPrefixCuts (2^48) 6829768705 10 Manual.Count131072.C052077.packed 64 cuts52077 = true := by
 decide +kernel
def cuts52078 : List PrefixCut := [⟨37,139502374,139502455⟩,
⟨64,237833084,237833223⟩]
theorem checked52078 : checkPrefixCuts (2^48) 6829899777 10 Manual.Count131072.C052078.packed 64 cuts52078 = true := by
 decide +kernel
def pointBounds52078 : List (Nat × Nat × Nat) := [(6829975552,112163333582202,112163720992244)]
theorem point_links_checked52078 : (cuts52078.take 1).map (fun c => (6829899777-1+2*2^10*c.k,112163194079828+c.lower,112163581489789+c.upper)) = pointBounds52078 := by
 decide +kernel
def cuts52079 : List PrefixCut := [⟨64,237746091,237746224⟩]
theorem checked52079 : checkPrefixCuts (2^48) 6830030849 10 Manual.Count131072.C052079.packed 64 cuts52079 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000064
