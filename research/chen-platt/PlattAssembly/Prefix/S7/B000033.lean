import PlattAssemblyKernel
import PlattCertificates.Count131072.C061056
import PlattCertificates.Count131072.C061057
import PlattCertificates.Count131072.C061058
import PlattCertificates.Count131072.C061059
import PlattCertificates.Count131072.C061060
import PlattCertificates.Count131072.C061061
import PlattCertificates.Count131072.C061062
import PlattCertificates.Count131072.C061063
import PlattCertificates.Count131072.C061064
import PlattCertificates.Count131072.C061065
import PlattCertificates.Count131072.C061066
import PlattCertificates.Count131072.C061067
import PlattCertificates.Count131072.C061068
import PlattCertificates.Count131072.C061069
import PlattCertificates.Count131072.C061070
import PlattCertificates.Count131072.C061071
import PlattCertificates.Count131072.C061072
import PlattCertificates.Count131072.C061073
import PlattCertificates.Count131072.C061074
import PlattCertificates.Count131072.C061075
import PlattCertificates.Count131072.C061076
import PlattCertificates.Count131072.C061077
import PlattCertificates.Count131072.C061078
import PlattCertificates.Count131072.C061079
import PlattCertificates.Count131072.C061080
import PlattCertificates.Count131072.C061081
import PlattCertificates.Count131072.C061082
import PlattCertificates.Count131072.C061083
import PlattCertificates.Count131072.C061084
import PlattCertificates.Count131072.C061085
import PlattCertificates.Count131072.C061086
import PlattCertificates.Count131072.C061087
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000033
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts61056 : List PrefixCut := [⟨64,205163353,205163469⟩]
theorem checked61056 : checkPrefixCuts (2^48) 8006664193 10 Manual.Count131072.C061056.packed 64 cuts61056 = true := by
 decide +kernel
def cuts61057 : List PrefixCut := [⟨35,109400316,109400380⟩,
⟨64,203331953,203332066⟩]
theorem checked61057 : checkPrefixCuts (2^48) 8006795265 10 Manual.Count131072.C061057.packed 64 cuts61057 = true := by
 decide +kernel
def pointBounds61057 : List (Nat × Nat × Nat) := [(8006866944,114132474187419,114132862717953)]
theorem point_links_checked61057 : (cuts61057.take 1).map (fun c => (8006795265-1+2*2^10*c.k,114132364787103+c.lower,114132753317573+c.upper)) = pointBounds61057 := by
 decide +kernel
def cuts61058 : List PrefixCut := [⟨64,200727284,200727397⟩]
theorem checked61058 : checkPrefixCuts (2^48) 8006926337 10 Manual.Count131072.C061058.packed 64 cuts61058 = true := by
 decide +kernel
def cuts61059 : List PrefixCut := [⟨30,95722210,95722263⟩,
⟨64,203430788,203430905⟩]
theorem checked61059 : checkPrefixCuts (2^48) 8007057409 10 Manual.Count131072.C061059.packed 64 cuts61059 = true := by
 decide +kernel
def pointBounds61059 : List (Nat × Nat × Nat) := [(8007118848,114132864568550,114133253099299)]
theorem point_links_checked61059 : (cuts61059.take 1).map (fun c => (8007057409-1+2*2^10*c.k,114132768846340+c.lower,114133157377036+c.upper)) = pointBounds61059 := by
 decide +kernel
def cuts61060 : List PrefixCut := [⟨64,202056495,202056608⟩]
theorem checked61060 : checkPrefixCuts (2^48) 8007188481 10 Manual.Count131072.C061060.packed 64 cuts61060 = true := by
 decide +kernel
def cuts61061 : List PrefixCut := [⟨25,79760083,79760126⟩,
⟨64,200787728,200787843⟩]
theorem checked61061 : checkPrefixCuts (2^48) 8007319553 10 Manual.Count131072.C061061.packed 64 cuts61061 = true := by
 decide +kernel
def pointBounds61061 : List (Nat × Nat × Nat) := [(8007370752,114133254093706,114133642624675)]
theorem point_links_checked61061 : (cuts61061.take 1).map (fun c => (8007319553-1+2*2^10*c.k,114133174333623+c.lower,114133562864549+c.upper)) = pointBounds61061 := by
 decide +kernel
def cuts61062 : List PrefixCut := [⟨64,203912923,203913036⟩]
theorem checked61062 : checkPrefixCuts (2^48) 8007450625 10 Manual.Count131072.C061062.packed 64 cuts61062 = true := by
 decide +kernel
def cuts61063 : List PrefixCut := [⟨20,63377177,63377215⟩,
⟨64,202468374,202468492⟩]
theorem checked61063 : checkPrefixCuts (2^48) 8007581697 10 Manual.Count131072.C061063.packed 64 cuts61063 = true := by
 decide +kernel
def pointBounds61063 : List (Nat × Nat × Nat) := [(8007622656,114133642411451,114134030942643)]
theorem point_links_checked61063 : (cuts61063.take 1).map (fun c => (8007581697-1+2*2^10*c.k,114133579034274+c.lower,114133967565428+c.upper)) = pointBounds61063 := by
 decide +kernel
def cuts61064 : List PrefixCut := [⟨64,203308659,203308778⟩]
theorem checked61064 : checkPrefixCuts (2^48) 8007712769 10 Manual.Count131072.C061064.packed 64 cuts61064 = true := by
 decide +kernel
def cuts61065 : List PrefixCut := [⟨15,48014669,48014697⟩,
⟨64,200212179,200212295⟩]
theorem checked61065 : checkPrefixCuts (2^48) 8007843841 10 Manual.Count131072.C061065.packed 64 cuts61065 = true := by
 decide +kernel
def pointBounds61065 : List (Nat × Nat × Nat) := [(8007874560,114134032825976,114134421357395)]
theorem point_links_checked61065 : (cuts61065.take 1).map (fun c => (8007843841-1+2*2^10*c.k,114133984811307+c.lower,114134373342698+c.upper)) = pointBounds61065 := by
 decide +kernel
def cuts61066 : List PrefixCut := [⟨64,201509422,201509534⟩]
theorem checked61066 : checkPrefixCuts (2^48) 8007974913 10 Manual.Count131072.C061066.packed 64 cuts61066 = true := by
 decide +kernel
def cuts61067 : List PrefixCut := [⟨10,33004633,33004649⟩,
⟨64,202384851,202384967⟩]
theorem checked61067 : checkPrefixCuts (2^48) 8008105985 10 Manual.Count131072.C061067.packed 64 cuts61067 = true := by
 decide +kernel
def pointBounds61067 : List (Nat × Nat × Nat) := [(8008126464,114134419537541,114134808069176)]
theorem point_links_checked61067 : (cuts61067.take 1).map (fun c => (8008105985-1+2*2^10*c.k,114134386532908+c.lower,114134775064527+c.upper)) = pointBounds61067 := by
 decide +kernel
def cuts61068 : List PrefixCut := [⟨64,204982456,204982573⟩]
theorem checked61068 : checkPrefixCuts (2^48) 8008237057 10 Manual.Count131072.C061068.packed 64 cuts61068 = true := by
 decide +kernel
def cuts61069 : List PrefixCut := [⟨5,15781260,15781270⟩,
⟨64,202448500,202448614⟩]
theorem checked61069 : checkPrefixCuts (2^48) 8008368129 10 Manual.Count131072.C061069.packed 64 cuts61069 = true := by
 decide +kernel
def pointBounds61069 : List (Nat × Nat × Nat) := [(8008378368,114134809681475,114135198213337)]
theorem point_links_checked61069 : (cuts61069.take 1).map (fun c => (8008368129-1+2*2^10*c.k,114134793900215+c.lower,114135182432067+c.upper)) = pointBounds61069 := by
 decide +kernel
def cuts61070 : List PrefixCut := [⟨64,201144767,201144879⟩]
theorem checked61070 : checkPrefixCuts (2^48) 8008499201 10 Manual.Count131072.C061070.packed 64 cuts61070 = true := by
 decide +kernel
def pointBounds61070 : List (Nat × Nat × Nat) := [(8008630272,114135197493482,114135586025560)]
theorem point_links_checked61070 : (cuts61070.take 1).map (fun c => (8008499201-1+2*2^10*c.k,114134996348715+c.lower,114135384880681+c.upper)) = pointBounds61070 := by
 decide +kernel
def cuts61071 : List PrefixCut := [⟨64,203882848,203882964⟩]
theorem checked61071 : checkPrefixCuts (2^48) 8008630273 10 Manual.Count131072.C061071.packed 64 cuts61071 = true := by
 decide +kernel
def cuts61072 : List PrefixCut := [⟨59,185849969,185850077⟩,
⟨64,201208473,201208589⟩]
theorem checked61072 : checkPrefixCuts (2^48) 8008761345 10 Manual.Count131072.C061072.packed 64 cuts61072 = true := by
 decide +kernel
def pointBounds61072 : List (Nat × Nat × Nat) := [(8008882176,114135587226299,114135975758601)]
theorem point_links_checked61072 : (cuts61072.take 1).map (fun c => (8008761345-1+2*2^10*c.k,114135401376330+c.lower,114135789908524+c.upper)) = pointBounds61072 := by
 decide +kernel
def cuts61073 : List PrefixCut := [⟨64,205106266,205106381⟩]
theorem checked61073 : checkPrefixCuts (2^48) 8008892417 10 Manual.Count131072.C061073.packed 64 cuts61073 = true := by
 decide +kernel
def cuts61074 : List PrefixCut := [⟨54,171891642,171891744⟩,
⟨64,202467088,202467209⟩]
theorem checked61074 : checkPrefixCuts (2^48) 8009023489 10 Manual.Count131072.C061074.packed 64 cuts61074 = true := by
 decide +kernel
def pointBounds61074 : List (Nat × Nat × Nat) := [(8009134080,114135979582711,114136368115238)]
theorem point_links_checked61074 : (cuts61074.take 1).map (fun c => (8009023489-1+2*2^10*c.k,114135807691069+c.lower,114136196223494+c.upper)) = pointBounds61074 := by
 decide +kernel
def cuts61075 : List PrefixCut := [⟨64,203974960,203975078⟩]
theorem checked61075 : checkPrefixCuts (2^48) 8009154561 10 Manual.Count131072.C061075.packed 64 cuts61075 = true := by
 decide +kernel
def cuts61076 : List PrefixCut := [⟨49,154911883,154911970⟩,
⟨64,203093019,203093133⟩]
theorem checked61076 : checkPrefixCuts (2^48) 8009285633 10 Manual.Count131072.C061076.packed 64 cuts61076 = true := by
 decide +kernel
def pointBounds61076 : List (Nat × Nat × Nat) := [(8009385984,114136369045000,114136757577751)]
theorem point_links_checked61076 : (cuts61076.take 1).map (fun c => (8009285633-1+2*2^10*c.k,114136214133117+c.lower,114136602665781+c.upper)) = pointBounds61076 := by
 decide +kernel
def cuts61077 : List PrefixCut := [⟨64,201156860,201156973⟩]
theorem checked61077 : checkPrefixCuts (2^48) 8009416705 10 Manual.Count131072.C061077.packed 64 cuts61077 = true := by
 decide +kernel
def cuts61078 : List PrefixCut := [⟨44,140147185,140147261⟩,
⟨64,200907591,200907701⟩]
theorem checked61078 : checkPrefixCuts (2^48) 8009547777 10 Manual.Count131072.C061078.packed 64 cuts61078 = true := by
 decide +kernel
def pointBounds61078 : List (Nat × Nat × Nat) := [(8009637888,114136758530181,114137147063148)]
theorem point_links_checked61078 : (cuts61078.take 1).map (fun c => (8009547777-1+2*2^10*c.k,114136618382996+c.lower,114137006915887+c.upper)) = pointBounds61078 := by
 decide +kernel
def cuts61079 : List PrefixCut := [⟨64,204383294,204383414⟩]
theorem checked61079 : checkPrefixCuts (2^48) 8009678849 10 Manual.Count131072.C061079.packed 64 cuts61079 = true := by
 decide +kernel
def cuts61080 : List PrefixCut := [⟨39,123696656,123696729⟩,
⟨64,201884954,201885072⟩]
theorem checked61080 : checkPrefixCuts (2^48) 8009809921 10 Manual.Count131072.C061080.packed 64 cuts61080 = true := by
 decide +kernel
def pointBounds61080 : List (Nat × Nat × Nat) := [(8009889792,114137147370537,114137535903731)]
theorem point_links_checked61080 : (cuts61080.take 1).map (fun c => (8009809921-1+2*2^10*c.k,114137023673881+c.lower,114137412207002+c.upper)) = pointBounds61080 := by
 decide +kernel
def cuts61081 : List PrefixCut := [⟨64,202619586,202619699⟩]
theorem checked61081 : checkPrefixCuts (2^48) 8009940993 10 Manual.Count131072.C061081.packed 64 cuts61081 = true := by
 decide +kernel
def cuts61082 : List PrefixCut := [⟨34,106579532,106579590⟩,
⟨64,200261923,200262032⟩]
theorem checked61082 : checkPrefixCuts (2^48) 8010072065 10 Manual.Count131072.C061082.packed 64 cuts61082 = true := by
 decide +kernel
def pointBounds61082 : List (Nat × Nat × Nat) := [(8010141696,114137534757953,114137923291363)]
theorem point_links_checked61082 : (cuts61082.take 1).map (fun c => (8010072065-1+2*2^10*c.k,114137428178421+c.lower,114137816711773+c.upper)) = pointBounds61082 := by
 decide +kernel
def cuts61083 : List PrefixCut := [⟨64,200012667,200012781⟩]
theorem checked61083 : checkPrefixCuts (2^48) 8010203137 10 Manual.Count131072.C061083.packed 64 cuts61083 = true := by
 decide +kernel
def cuts61084 : List PrefixCut := [⟨29,90341957,90342009⟩,
⟨64,202855602,202855717⟩]
theorem checked61084 : checkPrefixCuts (2^48) 8010334209 10 Manual.Count131072.C061084.packed 64 cuts61084 = true := by
 decide +kernel
def pointBounds61084 : List (Nat × Nat × Nat) := [(8010393600,114137918794968,114138307328595)]
theorem point_links_checked61084 : (cuts61084.take 1).map (fun c => (8010334209-1+2*2^10*c.k,114137828453011+c.lower,114138216986586+c.upper)) = pointBounds61084 := by
 decide +kernel
def cuts61085 : List PrefixCut := [⟨64,203238826,203238940⟩]
theorem checked61085 : checkPrefixCuts (2^48) 8010465281 10 Manual.Count131072.C061085.packed 64 cuts61085 = true := by
 decide +kernel
def cuts61086 : List PrefixCut := [⟨24,74351403,74351442⟩,
⟨64,202181355,202181469⟩]
theorem checked61086 : checkPrefixCuts (2^48) 8010596353 10 Manual.Count131072.C061086.packed 64 cuts61086 = true := by
 decide +kernel
def pointBounds61086 : List (Nat × Nat × Nat) := [(8010645504,114138308898842,114138697432685)]
theorem point_links_checked61086 : (cuts61086.take 1).map (fun c => (8010596353-1+2*2^10*c.k,114138234547439+c.lower,114138623081243+c.upper)) = pointBounds61086 := by
 decide +kernel
def cuts61087 : List PrefixCut := [⟨64,201651011,201651124⟩]
theorem checked61087 : checkPrefixCuts (2^48) 8010727425 10 Manual.Count131072.C061087.packed 64 cuts61087 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000033
