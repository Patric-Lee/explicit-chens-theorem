import PlattAssemblyKernel
import PlattCertificates.Count131072.C058000
import PlattCertificates.Count131072.C058001
import PlattCertificates.Count131072.C058002
import PlattCertificates.Count131072.C058003
import PlattCertificates.Count131072.C058004
import PlattCertificates.Count131072.C058005
import PlattCertificates.Count131072.C058006
import PlattCertificates.Count131072.C058007
import PlattCertificates.Count131072.C058008
import PlattCertificates.Count131072.C058009
import PlattCertificates.Count131072.C058010
import PlattCertificates.Count131072.C058011
import PlattCertificates.Count131072.C058012
import PlattCertificates.Count131072.C058013
import PlattCertificates.Count131072.C058014
import PlattCertificates.Count131072.C058015
import PlattCertificates.Count131072.C058016
import PlattCertificates.Count131072.C058017
import PlattCertificates.Count131072.C058018
import PlattCertificates.Count131072.C058019
import PlattCertificates.Count131072.C058020
import PlattCertificates.Count131072.C058021
import PlattCertificates.Count131072.C058022
import PlattCertificates.Count131072.C058023
import PlattCertificates.Count131072.C058024
import PlattCertificates.Count131072.C058025
import PlattCertificates.Count131072.C058026
import PlattCertificates.Count131072.C058027
import PlattCertificates.Count131072.C058028
import PlattCertificates.Count131072.C058029
import PlattCertificates.Count131072.C058030
import PlattCertificates.Count131072.C058031
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000250
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts58000 : List PrefixCut := [⟨24,79119491,79119536⟩,
⟨64,212785132,212785254⟩]
theorem checked58000 : checkPrefixCuts (2^48) 7606108161 10 Manual.Count131072.C058000.packed 64 cuts58000 = true := by
 decide +kernel
def pointBounds58000 : List (Nat × Nat × Nat) := [(7606157312,113497980086379,113498368254652)]
theorem point_links_checked58000 : (cuts58000.take 1).map (fun c => (7606108161-1+2*2^10*c.k,113497900966888+c.lower,113498289135116+c.upper)) = pointBounds58000 := by
 decide +kernel
def cuts58001 : List PrefixCut := [⟨64,211967353,211967478⟩]
theorem checked58001 : checkPrefixCuts (2^48) 7606239233 10 Manual.Count131072.C058001.packed 64 cuts58001 = true := by
 decide +kernel
def cuts58002 : List PrefixCut := [⟨13,44998188,44998213⟩,
⟨64,214850080,214850202⟩]
theorem checked58002 : checkPrefixCuts (2^48) 7606370305 10 Manual.Count131072.C058002.packed 64 cuts58002 = true := by
 decide +kernel
def pointBounds58002 : List (Nat × Nat × Nat) := [(7606396928,113498370717561,113498758886061)]
theorem point_links_checked58002 : (cuts58002.take 1).map (fun c => (7606370305-1+2*2^10*c.k,113498325719373+c.lower,113498713887848+c.upper)) = pointBounds58002 := by
 decide +kernel
def cuts58003 : List PrefixCut := [⟨64,212774129,212774252⟩]
theorem checked58003 : checkPrefixCuts (2^48) 7606501377 10 Manual.Count131072.C058003.packed 64 cuts58003 = true := by
 decide +kernel
def cuts58004 : List PrefixCut := [⟨2,7215754,7215758⟩,
⟨64,215619728,215619852⟩]
theorem checked58004 : checkPrefixCuts (2^48) 7606632449 10 Manual.Count131072.C058004.packed 64 cuts58004 = true := by
 decide +kernel
def pointBounds58004 : List (Nat × Nat × Nat) := [(7606636544,113498760559336,113499148728060)]
theorem point_links_checked58004 : (cuts58004.take 1).map (fun c => (7606632449-1+2*2^10*c.k,113498753343582+c.lower,113499141512302+c.upper)) = pointBounds58004 := by
 decide +kernel
def cuts58005 : List PrefixCut := [⟨55,183090664,183090766⟩,
⟨64,212951800,212951919⟩]
theorem checked58005 : checkPrefixCuts (2^48) 7606763521 10 Manual.Count131072.C058005.packed 64 cuts58005 = true := by
 decide +kernel
def pointBounds58005 : List (Nat × Nat × Nat) := [(7606876160,113499152053974,113499540222920)]
theorem point_links_checked58005 : (cuts58005.take 1).map (fun c => (7606763521-1+2*2^10*c.k,113498968963310+c.lower,113499357132154+c.upper)) = pointBounds58005 := by
 decide +kernel
def cuts58006 : List PrefixCut := [⟨64,212615124,212615244⟩]
theorem checked58006 : checkPrefixCuts (2^48) 7606894593 10 Manual.Count131072.C058006.packed 64 cuts58006 = true := by
 decide +kernel
def cuts58007 : List PrefixCut := [⟨44,148673011,148673093⟩,
⟨64,213240503,213240622⟩]
theorem checked58007 : checkPrefixCuts (2^48) 7607025665 10 Manual.Count131072.C058007.packed 64 cuts58007 = true := by
 decide +kernel
def pointBounds58007 : List (Nat × Nat × Nat) := [(7607115776,113499543203245,113499931372410)]
theorem point_links_checked58007 : (cuts58007.take 1).map (fun c => (7607025665-1+2*2^10*c.k,113499394530234+c.lower,113499782699317+c.upper)) = pointBounds58007 := by
 decide +kernel
def cuts58008 : List PrefixCut := [⟨64,214901854,214901977⟩]
theorem checked58008 : checkPrefixCuts (2^48) 7607156737 10 Manual.Count131072.C058008.packed 64 cuts58008 = true := by
 decide +kernel
def cuts58009 : List PrefixCut := [⟨33,109780556,109780620⟩,
⟨64,211272125,211272247⟩]
theorem checked58009 : checkPrefixCuts (2^48) 7607287809 10 Manual.Count131072.C058009.packed 64 cuts58009 = true := by
 decide +kernel
def pointBounds58009 : List (Nat × Nat × Nat) := [(7607355392,113499932453147,113500320622536)]
theorem point_links_checked58009 : (cuts58009.take 1).map (fun c => (7607287809-1+2*2^10*c.k,113499822672591+c.lower,113500210841916+c.upper)) = pointBounds58009 := by
 decide +kernel
def cuts58010 : List PrefixCut := [⟨64,213451483,213451606⟩]
theorem checked58010 : checkPrefixCuts (2^48) 7607418881 10 Manual.Count131072.C058010.packed 64 cuts58010 = true := by
 decide +kernel
def cuts58011 : List PrefixCut := [⟨22,72555639,72555680⟩,
⟨64,212855811,212855933⟩]
theorem checked58011 : checkPrefixCuts (2^48) 7607549953 10 Manual.Count131072.C058011.packed 64 cuts58011 = true := by
 decide +kernel
def pointBounds58011 : List (Nat × Nat × Nat) := [(7607595008,113500319951838,113500708121449)]
theorem point_links_checked58011 : (cuts58011.take 1).map (fun c => (7607549953-1+2*2^10*c.k,113500247396199+c.lower,113500635565769+c.upper)) = pointBounds58011 := by
 decide +kernel
def cuts58012 : List PrefixCut := [⟨64,211298196,211298316⟩]
theorem checked58012 : checkPrefixCuts (2^48) 7607681025 10 Manual.Count131072.C058012.packed 64 cuts58012 = true := by
 decide +kernel
def cuts58013 : List PrefixCut := [⟨11,37516058,37516080⟩,
⟨64,214217385,214217509⟩]
theorem checked58013 : checkPrefixCuts (2^48) 7607812097 10 Manual.Count131072.C058013.packed 64 cuts58013 = true := by
 decide +kernel
def pointBounds58013 : List (Nat × Nat × Nat) := [(7607834624,113500709066264,113501097236098)]
theorem point_links_checked58013 : (cuts58013.take 1).map (fun c => (7607812097-1+2*2^10*c.k,113500671550206+c.lower,113501059720018+c.upper)) = pointBounds58013 := by
 decide +kernel
def cuts58014 : List PrefixCut := [⟨64,214805639,214805761⟩]
theorem checked58014 : checkPrefixCuts (2^48) 7607943169 10 Manual.Count131072.C058014.packed 64 cuts58014 = true := by
 decide +kernel
def pointBounds58014 : List (Nat × Nat × Nat) := [(7608074240,113501100573230,113501488743288)]
theorem point_links_checked58014 : (cuts58014.take 1).map (fun c => (7607943169-1+2*2^10*c.k,113500885767591+c.lower,113501273937527+c.upper)) = pointBounds58014 := by
 decide +kernel
def cuts58015 : List PrefixCut := [⟨64,213618059,213618181⟩]
theorem checked58015 : checkPrefixCuts (2^48) 7608074241 10 Manual.Count131072.C058015.packed 64 cuts58015 = true := by
 decide +kernel
def cuts58016 : List PrefixCut := [⟨53,175212884,175212983⟩,
⟨64,212504494,212504615⟩]
theorem checked58016 : checkPrefixCuts (2^48) 7608205313 10 Manual.Count131072.C058016.packed 64 cuts58016 = true := by
 decide +kernel
def pointBounds58016 : List (Nat × Nat × Nat) := [(7608313856,113501489404173,113501877574452)]
theorem point_links_checked58016 : (cuts58016.take 1).map (fun c => (7608205313-1+2*2^10*c.k,113501314191289+c.lower,113501702361469+c.upper)) = pointBounds58016 := by
 decide +kernel
def cuts58017 : List PrefixCut := [⟨64,215941407,215941530⟩]
theorem checked58017 : checkPrefixCuts (2^48) 7608336385 10 Manual.Count131072.C058017.packed 64 cuts58017 = true := by
 decide +kernel
def cuts58018 : List PrefixCut := [⟨42,141171942,141172023⟩,
⟨64,213533040,213533164⟩]
theorem checked58018 : checkPrefixCuts (2^48) 7608467457 10 Manual.Count131072.C058018.packed 64 cuts58018 = true := by
 decide +kernel
def pointBounds58018 : List (Nat × Nat × Nat) := [(7608553472,113501883809132,113502271979637)]
theorem point_links_checked58018 : (cuts58018.take 1).map (fun c => (7608467457-1+2*2^10*c.k,113501742637190+c.lower,113502130807614+c.upper)) = pointBounds58018 := by
 decide +kernel
def cuts58019 : List PrefixCut := [⟨64,213973275,213973397⟩]
theorem checked58019 : checkPrefixCuts (2^48) 7608598529 10 Manual.Count131072.C058019.packed 64 cuts58019 = true := by
 decide +kernel
def cuts58020 : List PrefixCut := [⟨31,102287091,102287149⟩,
⟨64,213303696,213303818⟩]
theorem checked58020 : checkPrefixCuts (2^48) 7608729601 10 Manual.Count131072.C058020.packed 64 cuts58020 = true := by
 decide +kernel
def pointBounds58020 : List (Nat × Nat × Nat) := [(7608793088,113502272430596,113502660601324)]
theorem point_links_checked58020 : (cuts58020.take 1).map (fun c => (7608729601-1+2*2^10*c.k,113502170143505+c.lower,113502558314175+c.upper)) = pointBounds58020 := by
 decide +kernel
def cuts58021 : List PrefixCut := [⟨64,209304813,209304937⟩]
theorem checked58021 : checkPrefixCuts (2^48) 7608860673 10 Manual.Count131072.C058021.packed 64 cuts58021 = true := by
 decide +kernel
def cuts58022 : List PrefixCut := [⟨20,66956068,66956105⟩,
⟨64,213370354,213370475⟩]
theorem checked58022 : checkPrefixCuts (2^48) 7608991745 10 Manual.Count131072.C058022.packed 64 cuts58022 = true := by
 decide +kernel
def pointBounds58022 : List (Nat × Nat × Nat) := [(7609032704,113502659708082,113503047879035)]
theorem point_links_checked58022 : (cuts58022.take 1).map (fun c => (7608991745-1+2*2^10*c.k,113502592752014+c.lower,113502980922930+c.upper)) = pointBounds58022 := by
 decide +kernel
def cuts58023 : List PrefixCut := [⟨64,213366668,213366790⟩]
theorem checked58023 : checkPrefixCuts (2^48) 7609122817 10 Manual.Count131072.C058023.packed 64 cuts58023 = true := by
 decide +kernel
def cuts58024 : List PrefixCut := [⟨9,30110743,30110761⟩,
⟨64,212771149,212771274⟩]
theorem checked58024 : checkPrefixCuts (2^48) 7609253889 10 Manual.Count131072.C058024.packed 64 cuts58024 = true := by
 decide +kernel
def pointBounds58024 : List (Nat × Nat × Nat) := [(7609272320,113503049599779,113503437770956)]
theorem point_links_checked58024 : (cuts58024.take 1).map (fun c => (7609253889-1+2*2^10*c.k,113503019489036+c.lower,113503407660195+c.upper)) = pointBounds58024 := by
 decide +kernel
def cuts58025 : List PrefixCut := [⟨62,205850369,205850486⟩,
⟨64,212693494,212693614⟩]
theorem checked58025 : checkPrefixCuts (2^48) 7609384961 10 Manual.Count131072.C058025.packed 64 cuts58025 = true := by
 decide +kernel
def pointBounds58025 : List (Nat × Nat × Nat) := [(7609511936,113503438110554,113503826281955)]
theorem point_links_checked58025 : (cuts58025.take 1).map (fun c => (7609384961-1+2*2^10*c.k,113503232260185+c.lower,113503620431469+c.upper)) = pointBounds58025 := by
 decide +kernel
def cuts58026 : List PrefixCut := [⟨64,212024026,212024144⟩]
theorem checked58026 : checkPrefixCuts (2^48) 7609516033 10 Manual.Count131072.C058026.packed 64 cuts58026 = true := by
 decide +kernel
def cuts58027 : List PrefixCut := [⟨51,169742359,169742457⟩,
⟨64,212612202,212612325⟩]
theorem checked58027 : checkPrefixCuts (2^48) 7609647105 10 Manual.Count131072.C058027.packed 64 cuts58027 = true := by
 decide +kernel
def pointBounds58027 : List (Nat × Nat × Nat) := [(7609751552,113503826720064,113504214891684)]
theorem point_links_checked58027 : (cuts58027.take 1).map (fun c => (7609647105-1+2*2^10*c.k,113503656977705+c.lower,113504045149227+c.upper)) = pointBounds58027 := by
 decide +kernel
def cuts58028 : List PrefixCut := [⟨64,212682516,212682640⟩]
theorem checked58028 : checkPrefixCuts (2^48) 7609778177 10 Manual.Count131072.C058028.packed 64 cuts58028 = true := by
 decide +kernel
def cuts58029 : List PrefixCut := [⟨40,135153213,135153290⟩,
⟨64,215822792,215822914⟩]
theorem checked58029 : checkPrefixCuts (2^48) 7609909249 10 Manual.Count131072.C058029.packed 64 cuts58029 = true := by
 decide +kernel
def pointBounds58029 : List (Nat × Nat × Nat) := [(7609991168,113504217425636,113504605597482)]
theorem point_links_checked58029 : (cuts58029.take 1).map (fun c => (7609909249-1+2*2^10*c.k,113504082272423+c.lower,113504470444192+c.upper)) = pointBounds58029 := by
 decide +kernel
def cuts58030 : List PrefixCut := [⟨64,212638201,212638326⟩]
theorem checked58030 : checkPrefixCuts (2^48) 7610040321 10 Manual.Count131072.C058030.packed 64 cuts58030 = true := by
 decide +kernel
def cuts58031 : List PrefixCut := [⟨29,98606069,98606126⟩,
⟨64,214927686,214927811⟩]
theorem checked58031 : checkPrefixCuts (2^48) 7610171393 10 Manual.Count131072.C058031.packed 64 cuts58031 = true := by
 decide +kernel
def pointBounds58031 : List (Nat × Nat × Nat) := [(7610230784,113504609339485,113504997511558)]
theorem point_links_checked58031 : (cuts58031.take 1).map (fun c => (7610171393-1+2*2^10*c.k,113504510733416+c.lower,113504898905432+c.upper)) = pointBounds58031 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000250
