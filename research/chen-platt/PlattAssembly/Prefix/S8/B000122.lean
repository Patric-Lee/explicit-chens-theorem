import PlattAssemblyKernel
import PlattCertificates.Count131072.C073904
import PlattCertificates.Count131072.C073905
import PlattCertificates.Count131072.C073906
import PlattCertificates.Count131072.C073907
import PlattCertificates.Count131072.C073908
import PlattCertificates.Count131072.C073909
import PlattCertificates.Count131072.C073910
import PlattCertificates.Count131072.C073911
import PlattCertificates.Count131072.C073912
import PlattCertificates.Count131072.C073913
import PlattCertificates.Count131072.C073914
import PlattCertificates.Count131072.C073915
import PlattCertificates.Count131072.C073916
import PlattCertificates.Count131072.C073917
import PlattCertificates.Count131072.C073918
import PlattCertificates.Count131072.C073919
import PlattCertificates.Count131072.C073920
import PlattCertificates.Count131072.C073921
import PlattCertificates.Count131072.C073922
import PlattCertificates.Count131072.C073923
import PlattCertificates.Count131072.C073924
import PlattCertificates.Count131072.C073925
import PlattCertificates.Count131072.C073926
import PlattCertificates.Count131072.C073927
import PlattCertificates.Count131072.C073928
import PlattCertificates.Count131072.C073929
import PlattCertificates.Count131072.C073930
import PlattCertificates.Count131072.C073931
import PlattCertificates.Count131072.C073932
import PlattCertificates.Count131072.C073933
import PlattCertificates.Count131072.C073934
import PlattCertificates.Count131072.C073935
namespace ChenEffective.PlattWindow.Assembly.Prefix.S8.B000122
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts73904 : List PrefixCut := [⟨64,163934217,163934312⟩]
theorem checked73904 : checkPrefixCuts (2^48) 9690677249 10 Manual.Count131072.C073904.packed 64 cuts73904 = true := by
 decide +kernel
def cuts73905 : List PrefixCut := [⟨62,159865688,159865778⟩,
⟨64,165209998,165210092⟩]
theorem checked73905 : checkPrefixCuts (2^48) 9690808321 10 Manual.Count131072.C073905.packed 64 cuts73905 = true := by
 decide +kernel
def pointBounds73905 : List (Nat × Nat × Nat) := [(9690935296,116478965089276,116479354989089)]
theorem point_links_checked73905 : (cuts73905.take 1).map (fun c => (9690808321-1+2*2^10*c.k,116478805223588+c.lower,116479195123311+c.upper)) = pointBounds73905 := by
 decide +kernel
def cuts73906 : List PrefixCut := [⟨64,164481644,164481740⟩]
theorem checked73906 : checkPrefixCuts (2^48) 9690939393 10 Manual.Count131072.C073906.packed 64 cuts73906 = true := by
 decide +kernel
def cuts73907 : List PrefixCut := [⟨64,166076863,166076965⟩]
theorem checked73907 : checkPrefixCuts (2^48) 9691070465 10 Manual.Count131072.C073907.packed 64 cuts73907 = true := by
 decide +kernel
def cuts73908 : List PrefixCut := [⟨18,47574593,47574627⟩,
⟨64,165116157,165116261⟩]
theorem checked73908 : checkPrefixCuts (2^48) 9691201537 10 Manual.Count131072.C073908.packed 64 cuts73908 = true := by
 decide +kernel
def pointBounds73908 : List (Nat × Nat × Nat) := [(9691238400,116479348566686,116479738466735)]
theorem point_links_checked73908 : (cuts73908.take 1).map (fun c => (9691201537-1+2*2^10*c.k,116479300992093+c.lower,116479690892108+c.upper)) = pointBounds73908 := by
 decide +kernel
def cuts73909 : List PrefixCut := [⟨64,166914639,166914737⟩]
theorem checked73909 : checkPrefixCuts (2^48) 9691332609 10 Manual.Count131072.C073909.packed 64 cuts73909 = true := by
 decide +kernel
def cuts73910 : List PrefixCut := [⟨38,99938595,99938647⟩,
⟨64,170339495,170339588⟩]
theorem checked73910 : checkPrefixCuts (2^48) 9691463681 10 Manual.Count131072.C073910.packed 64 cuts73910 = true := by
 decide +kernel
def pointBounds73910 : List (Nat × Nat × Nat) := [(9691541504,116479732961484,116480122861753)]
theorem point_links_checked73910 : (cuts73910.take 1).map (fun c => (9691463681-1+2*2^10*c.k,116479633022889+c.lower,116480022923106+c.upper)) = pointBounds73910 := by
 decide +kernel
def cuts73911 : List PrefixCut := [⟨64,163802529,163802627⟩]
theorem checked73911 : checkPrefixCuts (2^48) 9691594753 10 Manual.Count131072.C073911.packed 64 cuts73911 = true := by
 decide +kernel
def cuts73912 : List PrefixCut := [⟨58,151079749,151079833⟩,
⟨64,167053084,167053179⟩]
theorem checked73912 : checkPrefixCuts (2^48) 9691725825 10 Manual.Count131072.C073912.packed 64 cuts73912 = true := by
 decide +kernel
def pointBounds73912 : List (Nat × Nat × Nat) := [(9691844608,116480118244662,116480508145154)]
theorem point_links_checked73912 : (cuts73912.take 1).map (fun c => (9691725825-1+2*2^10*c.k,116479967164913+c.lower,116480357065321+c.upper)) = pointBounds73912 := by
 decide +kernel
def cuts73913 : List PrefixCut := [⟨64,164872654,164872753⟩]
theorem checked73913 : checkPrefixCuts (2^48) 9691856897 10 Manual.Count131072.C073913.packed 64 cuts73913 = true := by
 decide +kernel
def cuts73914 : List PrefixCut := [⟨64,164986588,164986687⟩]
theorem checked73914 : checkPrefixCuts (2^48) 9691987969 10 Manual.Count131072.C073914.packed 64 cuts73914 = true := by
 decide +kernel
def cuts73915 : List PrefixCut := [⟨14,38015431,38015452⟩,
⟨64,167685228,167685324⟩]
theorem checked73915 : checkPrefixCuts (2^48) 9692119041 10 Manual.Count131072.C073915.packed 64 cuts73915 = true := by
 decide +kernel
def pointBounds73915 : List (Nat × Nat × Nat) := [(9692147712,116480502092670,116480891993392)]
theorem point_links_checked73915 : (cuts73915.take 1).map (fun c => (9692119041-1+2*2^10*c.k,116480464077239+c.lower,116480853977940+c.upper)) = pointBounds73915 := by
 decide +kernel
def cuts73916 : List PrefixCut := [⟨64,167508696,167508800⟩]
theorem checked73916 : checkPrefixCuts (2^48) 9692250113 10 Manual.Count131072.C073916.packed 64 cuts73916 = true := by
 decide +kernel
def cuts73917 : List PrefixCut := [⟨34,87296454,87296507⟩,
⟨64,162598575,162598670⟩]
theorem checked73917 : checkPrefixCuts (2^48) 9692381185 10 Manual.Count131072.C073917.packed 64 cuts73917 = true := by
 decide +kernel
def pointBounds73917 : List (Nat × Nat × Nat) := [(9692450816,116480886567617,116481276468571)]
theorem point_links_checked73917 : (cuts73917.take 1).map (fun c => (9692381185-1+2*2^10*c.k,116480799271163+c.lower,116481189172064+c.upper)) = pointBounds73917 := by
 decide +kernel
def cuts73918 : List PrefixCut := [⟨64,164890552,164890655⟩]
theorem checked73918 : checkPrefixCuts (2^48) 9692512257 10 Manual.Count131072.C073918.packed 64 cuts73918 = true := by
 decide +kernel
def cuts73919 : List PrefixCut := [⟨54,139420508,139420593⟩,
⟨64,165323915,165324013⟩]
theorem checked73919 : checkPrefixCuts (2^48) 9692643329 10 Manual.Count131072.C073919.packed 64 cuts73919 = true := by
 decide +kernel
def pointBounds73919 : List (Nat × Nat × Nat) := [(9692753920,116481266180798,116481656081982)]
theorem point_links_checked73919 : (cuts73919.take 1).map (fun c => (9692643329-1+2*2^10*c.k,116481126760290+c.lower,116481516661389+c.upper)) = pointBounds73919 := by
 decide +kernel
def cuts73920 : List PrefixCut := [⟨64,165408794,165408900⟩]
theorem checked73920 : checkPrefixCuts (2^48) 9692774401 10 Manual.Count131072.C073920.packed 64 cuts73920 = true := by
 decide +kernel
def cuts73921 : List PrefixCut := [⟨64,166887548,166887649⟩]
theorem checked73921 : checkPrefixCuts (2^48) 9692905473 10 Manual.Count131072.C073921.packed 64 cuts73921 = true := by
 decide +kernel
def cuts73922 : List PrefixCut := [⟨10,26919012,26919026⟩,
⟨64,164823560,164823655⟩]
theorem checked73922 : checkPrefixCuts (2^48) 9693036545 10 Manual.Count131072.C073922.packed 64 cuts73922 = true := by
 decide +kernel
def pointBounds73922 : List (Nat × Nat × Nat) := [(9693057024,116481651299559,116482041200977)]
theorem point_links_checked73922 : (cuts73922.take 1).map (fun c => (9693036545-1+2*2^10*c.k,116481624380547+c.lower,116482014281951+c.upper)) = pointBounds73922 := by
 decide +kernel
def cuts73923 : List PrefixCut := [⟨64,164298628,164298731⟩]
theorem checked73923 : checkPrefixCuts (2^48) 9693167617 10 Manual.Count131072.C073923.packed 64 cuts73923 = true := by
 decide +kernel
def cuts73924 : List PrefixCut := [⟨30,77357227,77357273⟩,
⟨64,164354480,164354582⟩]
theorem checked73924 : checkPrefixCuts (2^48) 9693298689 10 Manual.Count131072.C073924.packed 64 cuts73924 = true := by
 decide +kernel
def pointBounds73924 : List (Nat × Nat × Nat) := [(9693360128,116482030859962,116482420761610)]
theorem point_links_checked73924 : (cuts73924.take 1).map (fun c => (9693298689-1+2*2^10*c.k,116481953502735+c.lower,116482343404337+c.upper)) = pointBounds73924 := by
 decide +kernel
def cuts73925 : List PrefixCut := [⟨64,164352276,164352377⟩]
theorem checked73925 : checkPrefixCuts (2^48) 9693429761 10 Manual.Count131072.C073925.packed 64 cuts73925 = true := by
 decide +kernel
def cuts73926 : List PrefixCut := [⟨50,130057406,130057478⟩,
⟨64,165801900,165801992⟩]
theorem checked73926 : checkPrefixCuts (2^48) 9693560833 10 Manual.Count131072.C073926.packed 64 cuts73926 = true := by
 decide +kernel
def pointBounds73926 : List (Nat × Nat × Nat) := [(9693663232,116482412266897,116482802168774)]
theorem point_links_checked73926 : (cuts73926.take 1).map (fun c => (9693560833-1+2*2^10*c.k,116482282209491+c.lower,116482672111296+c.upper)) = pointBounds73926 := by
 decide +kernel
def cuts73927 : List PrefixCut := [⟨64,167106294,167106391⟩]
theorem checked73927 : checkPrefixCuts (2^48) 9693691905 10 Manual.Count131072.C073927.packed 64 cuts73927 = true := by
 decide +kernel
def cuts73928 : List PrefixCut := [⟨64,161006416,161006517⟩]
theorem checked73928 : checkPrefixCuts (2^48) 9693822977 10 Manual.Count131072.C073928.packed 64 cuts73928 = true := by
 decide +kernel
def cuts73929 : List PrefixCut := [⟨6,15331066,15331074⟩,
⟨64,163733611,163733710⟩]
theorem checked73929 : checkPrefixCuts (2^48) 9693954049 10 Manual.Count131072.C073929.packed 64 cuts73929 = true := by
 decide +kernel
def pointBounds73929 : List (Nat × Nat × Nat) := [(9693966336,116482791455167,116483181357270)]
theorem point_links_checked73929 : (cuts73929.take 1).map (fun c => (9693954049-1+2*2^10*c.k,116482776124101+c.lower,116483166026196+c.upper)) = pointBounds73929 := by
 decide +kernel
def cuts73930 : List PrefixCut := [⟨64,165763888,165763982⟩]
theorem checked73930 : checkPrefixCuts (2^48) 9694085121 10 Manual.Count131072.C073930.packed 64 cuts73930 = true := by
 decide +kernel
def cuts73931 : List PrefixCut := [⟨26,67536021,67536063⟩,
⟨64,163845333,163845438⟩]
theorem checked73931 : checkPrefixCuts (2^48) 9694216193 10 Manual.Count131072.C073931.packed 64 cuts73931 = true := by
 decide +kernel
def pointBounds73931 : List (Nat × Nat × Nat) := [(9694269440,116483173157621,116483563059951)]
theorem point_links_checked73931 : (cuts73931.take 1).map (fun c => (9694216193-1+2*2^10*c.k,116483105621600+c.lower,116483495523888+c.upper)) = pointBounds73931 := by
 decide +kernel
def cuts73932 : List PrefixCut := [⟨64,168285441,168285540⟩]
theorem checked73932 : checkPrefixCuts (2^48) 9694347265 10 Manual.Count131072.C073932.packed 64 cuts73932 = true := by
 decide +kernel
def cuts73933 : List PrefixCut := [⟨46,121363864,121363934⟩,
⟨64,167005661,167005756⟩]
theorem checked73933 : checkPrefixCuts (2^48) 9694478337 10 Manual.Count131072.C073933.packed 64 cuts73933 = true := by
 decide +kernel
def pointBounds73933 : List (Nat × Nat × Nat) := [(9694572544,116483559116238,116483949018800)]
theorem point_links_checked73933 : (cuts73933.take 1).map (fun c => (9694478337-1+2*2^10*c.k,116483437752374+c.lower,116483827654866+c.upper)) = pointBounds73933 := by
 decide +kernel
def cuts73934 : List PrefixCut := [⟨64,165406520,165406621⟩]
theorem checked73934 : checkPrefixCuts (2^48) 9694609409 10 Manual.Count131072.C073934.packed 64 cuts73934 = true := by
 decide +kernel
def cuts73935 : List PrefixCut := [⟨64,164823617,164823716⟩]
theorem checked73935 : checkPrefixCuts (2^48) 9694740481 10 Manual.Count131072.C073935.packed 64 cuts73935 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S8.B000122
