import PlattAssemblyKernel
import PlattCertificates.Count131072.C040000
import PlattCertificates.Count131072.C040001
import PlattCertificates.Count131072.C040002
import PlattCertificates.Count131072.C040003
import PlattCertificates.Count131072.C040004
import PlattCertificates.Count131072.C040005
import PlattCertificates.Count131072.C040006
import PlattCertificates.Count131072.C040007
import PlattCertificates.Count131072.C040008
import PlattCertificates.Count131072.C040009
import PlattCertificates.Count131072.C040010
import PlattCertificates.Count131072.C040011
import PlattCertificates.Count131072.C040012
import PlattCertificates.Count131072.C040013
import PlattCertificates.Count131072.C040014
import PlattCertificates.Count131072.C040015
import PlattCertificates.Count131072.C040016
import PlattCertificates.Count131072.C040017
import PlattCertificates.Count131072.C040018
import PlattCertificates.Count131072.C040019
import PlattCertificates.Count131072.C040020
import PlattCertificates.Count131072.C040021
import PlattCertificates.Count131072.C040022
import PlattCertificates.Count131072.C040023
import PlattCertificates.Count131072.C040024
import PlattCertificates.Count131072.C040025
import PlattCertificates.Count131072.C040026
import PlattCertificates.Count131072.C040027
import PlattCertificates.Count131072.C040028
import PlattCertificates.Count131072.C040029
import PlattCertificates.Count131072.C040030
import PlattCertificates.Count131072.C040031
namespace ChenEffective.PlattWindow.Assembly.Prefix.S5.B000000
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts40000 : List PrefixCut := [⟨27,132024181,132024262⟩,
⟨64,314634780,314634971⟩]
theorem checked40000 : checkPrefixCuts (2^48) 5246812161 10 Manual.Count131072.C040000.packed 64 cuts40000 = true := by
 decide +kernel
def pointBounds40000 : List (Nat × Nat × Nat) := [(5246867456,108866354860239,108866740365917)]
theorem point_links_checked40000 : (cuts40000.take 1).map (fun c => (5246812161-1+2*2^10*c.k,108866222836058+c.lower,108866608341655+c.upper)) = pointBounds40000 := by
 decide +kernel
def cuts40001 : List PrefixCut := [⟨44,217530625,217530754⟩,
⟨64,316558129,316558317⟩]
theorem checked40001 : checkPrefixCuts (2^48) 5246943233 10 Manual.Count131072.C040001.packed 64 cuts40001 = true := by
 decide +kernel
def pointBounds40001 : List (Nat × Nat × Nat) := [(5247033344,108866755001463,108867140507380)]
theorem point_links_checked40001 : (cuts40001.take 1).map (fun c => (5246943233-1+2*2^10*c.k,108866537470838+c.lower,108866922976626+c.upper)) = pointBounds40001 := by
 decide +kernel
def cuts40002 : List PrefixCut := [⟨61,299223574,299223752⟩,
⟨64,314565430,314565617⟩]
theorem checked40002 : checkPrefixCuts (2^48) 5247074305 10 Manual.Count131072.C040002.packed 64 cuts40002 = true := by
 decide +kernel
def pointBounds40002 : List (Nat × Nat × Nat) := [(5247199232,108867153252541,108867538758695)]
theorem point_links_checked40002 : (cuts40002.take 1).map (fun c => (5247074305-1+2*2^10*c.k,108866854028967+c.lower,108867239534943+c.upper)) = pointBounds40002 := by
 decide +kernel
def cuts40003 : List PrefixCut := [⟨64,314128428,314128613⟩]
theorem checked40003 : checkPrefixCuts (2^48) 5247205377 10 Manual.Count131072.C040003.packed 64 cuts40003 = true := by
 decide +kernel
def cuts40004 : List PrefixCut := [⟨14,67534438,67534479⟩,
⟨64,312833209,312833397⟩]
theorem checked40004 : checkPrefixCuts (2^48) 5247336449 10 Manual.Count131072.C040004.packed 64 cuts40004 = true := by
 decide +kernel
def pointBounds40004 : List (Nat × Nat × Nat) := [(5247365120,108867550257263,108867935763652)]
theorem point_links_checked40004 : (cuts40004.take 1).map (fun c => (5247336449-1+2*2^10*c.k,108867482722825+c.lower,108867868229173+c.upper)) = pointBounds40004 := by
 decide +kernel
def cuts40005 : List PrefixCut := [⟨31,148957760,148957850⟩,
⟨64,313844502,313844689⟩]
theorem checked40005 : checkPrefixCuts (2^48) 5247467521 10 Manual.Count131072.C040005.packed 64 cuts40005 = true := by
 decide +kernel
def pointBounds40005 : List (Nat × Nat × Nat) := [(5247531008,108867944513794,108868330020420)]
theorem point_links_checked40005 : (cuts40005.take 1).map (fun c => (5247467521-1+2*2^10*c.k,108867795556034+c.lower,108868181062570+c.upper)) = pointBounds40005 := by
 decide +kernel
def cuts40006 : List PrefixCut := [⟨48,234560297,234560437⟩,
⟨64,312549412,312549598⟩]
theorem checked40006 : checkPrefixCuts (2^48) 5247598593 10 Manual.Count131072.C040006.packed 64 cuts40006 = true := by
 decide +kernel
def pointBounds40006 : List (Nat × Nat × Nat) := [(5247696896,108868343960833,108868729467696)]
theorem point_links_checked40006 : (cuts40006.take 1).map (fun c => (5247598593-1+2*2^10*c.k,108868109400536+c.lower,108868494907259+c.upper)) = pointBounds40006 := by
 decide +kernel
def cuts40007 : List PrefixCut := [⟨64,314043388,314043572⟩]
theorem checked40007 : checkPrefixCuts (2^48) 5247729665 10 Manual.Count131072.C040007.packed 64 cuts40007 = true := by
 decide +kernel
def cuts40008 : List PrefixCut := [⟨1,4666342,4666344⟩,
⟨64,314732795,314732979⟩]
theorem checked40008 : checkPrefixCuts (2^48) 5247860737 10 Manual.Count131072.C040008.packed 64 cuts40008 = true := by
 decide +kernel
def pointBounds40008 : List (Nat × Nat × Nat) := [(5247862784,108868740659678,108869126166773)]
theorem point_links_checked40008 : (cuts40008.take 1).map (fun c => (5247860737-1+2*2^10*c.k,108868735993336+c.lower,108869121500429+c.upper)) = pointBounds40008 := by
 decide +kernel
def cuts40009 : List PrefixCut := [⟨18,87424388,87424438⟩,
⟨64,313545017,313545205⟩]
theorem checked40009 : checkPrefixCuts (2^48) 5247991809 10 Manual.Count131072.C040009.packed 64 cuts40009 = true := by
 decide +kernel
def pointBounds40009 : List (Nat × Nat × Nat) := [(5248028672,108869138150519,108869523657846)]
theorem point_links_checked40009 : (cuts40009.take 1).map (fun c => (5247991809-1+2*2^10*c.k,108869050726131+c.lower,108869436233408+c.upper)) = pointBounds40009 := by
 decide +kernel
def cuts40010 : List PrefixCut := [⟨35,171411293,171411393⟩,
⟨64,315307035,315307222⟩]
theorem checked40010 : checkPrefixCuts (2^48) 5248122881 10 Manual.Count131072.C040010.packed 64 cuts40010 = true := by
 decide +kernel
def pointBounds40010 : List (Nat × Nat × Nat) := [(5248194560,108869535682441,108869921190006)]
theorem point_links_checked40010 : (cuts40010.take 1).map (fun c => (5248122881-1+2*2^10*c.k,108869364271148+c.lower,108869749778613+c.upper)) = pointBounds40010 := by
 decide +kernel
def cuts40011 : List PrefixCut := [⟨52,254320830,254320980⟩,
⟨64,313207544,313207730⟩]
theorem checked40011 : checkPrefixCuts (2^48) 5248253953 10 Manual.Count131072.C040011.packed 64 cuts40011 = true := by
 decide +kernel
def pointBounds40011 : List (Nat × Nat × Nat) := [(5248360448,108869933899013,108870319406815)]
theorem point_links_checked40011 : (cuts40011.take 1).map (fun c => (5248253953-1+2*2^10*c.k,108869679578183+c.lower,108870065085835+c.upper)) = pointBounds40011 := by
 decide +kernel
def cuts40012 : List PrefixCut := [⟨64,314057842,314058028⟩]
theorem checked40012 : checkPrefixCuts (2^48) 5248385025 10 Manual.Count131072.C040012.packed 64 cuts40012 = true := by
 decide +kernel
def cuts40013 : List PrefixCut := [⟨5,24294105,24294120⟩,
⟨64,316892315,316892507⟩]
theorem checked40013 : checkPrefixCuts (2^48) 5248516097 10 Manual.Count131072.C040013.packed 64 cuts40013 = true := by
 decide +kernel
def pointBounds40013 : List (Nat × Nat × Nat) := [(5248526336,108870331137674,108870716645713)]
theorem point_links_checked40013 : (cuts40013.take 1).map (fun c => (5248516097-1+2*2^10*c.k,108870306843569+c.lower,108870692351593+c.upper)) = pointBounds40013 := by
 decide +kernel
def cuts40014 : List PrefixCut := [⟨22,108971800,108971866⟩,
⟨64,314095772,314095961⟩]
theorem checked40014 : checkPrefixCuts (2^48) 5248647169 10 Manual.Count131072.C040014.packed 64 cuts40014 = true := by
 decide +kernel
def pointBounds40014 : List (Nat × Nat × Nat) := [(5248692224,108870732707684,108871118215966)]
theorem point_links_checked40014 : (cuts40014.take 1).map (fun c => (5248647169-1+2*2^10*c.k,108870623735884+c.lower,108871009244100+c.upper)) = pointBounds40014 := by
 decide +kernel
def cuts40015 : List PrefixCut := [⟨39,195360758,195360877⟩,
⟨64,315911269,315911459⟩]
theorem checked40015 : checkPrefixCuts (2^48) 5248778241 10 Manual.Count131072.C040015.packed 64 cuts40015 = true := by
 decide +kernel
def pointBounds40015 : List (Nat × Nat × Nat) := [(5248858112,108871133192414,108871518700938)]
theorem point_links_checked40015 : (cuts40015.take 1).map (fun c => (5248778241-1+2*2^10*c.k,108870937831656+c.lower,108871323340061+c.upper)) = pointBounds40015 := by
 decide +kernel
def cuts40016 : List PrefixCut := [⟨56,275309852,275310016⟩,
⟨64,313919238,313919426⟩]
theorem checked40016 : checkPrefixCuts (2^48) 5248909313 10 Manual.Count131072.C040016.packed 64 cuts40016 = true := by
 decide +kernel
def pointBounds40016 : List (Nat × Nat × Nat) := [(5249024000,108871529052777,108871914561536)]
theorem point_links_checked40016 : (cuts40016.take 1).map (fun c => (5248909313-1+2*2^10*c.k,108871253742925+c.lower,108871639251520+c.upper)) = pointBounds40016 := by
 decide +kernel
def cuts40017 : List PrefixCut := [⟨64,311927317,311927498⟩]
theorem checked40017 : checkPrefixCuts (2^48) 5249040385 10 Manual.Count131072.C040017.packed 64 cuts40017 = true := by
 decide +kernel
def cuts40018 : List PrefixCut := [⟨9,42629993,42630020⟩,
⟨64,311812250,311812435⟩]
theorem checked40018 : checkPrefixCuts (2^48) 5249171457 10 Manual.Count131072.C040018.packed 64 cuts40018 = true := by
 decide +kernel
def pointBounds40018 : List (Nat × Nat × Nat) := [(5249189888,108871922219473,108872307728464)]
theorem point_links_checked40018 : (cuts40018.take 1).map (fun c => (5249171457-1+2*2^10*c.k,108871879589480+c.lower,108872265098444+c.upper)) = pointBounds40018 := by
 decide +kernel
def cuts40019 : List PrefixCut := [⟨26,128047229,128047305⟩,
⟨64,315879659,315879845⟩]
theorem checked40019 : checkPrefixCuts (2^48) 5249302529 10 Manual.Count131072.C040019.packed 64 cuts40019 = true := by
 decide +kernel
def pointBounds40019 : List (Nat × Nat × Nat) := [(5249355776,108872319448959,108872704958184)]
theorem point_links_checked40019 : (cuts40019.take 1).map (fun c => (5249302529-1+2*2^10*c.k,108872191401730+c.lower,108872576910879+c.upper)) = pointBounds40019 := by
 decide +kernel
def cuts40020 : List PrefixCut := [⟨43,213352385,213352509⟩,
⟨64,317533969,317534156⟩]
theorem checked40020 : checkPrefixCuts (2^48) 5249433601 10 Manual.Count131072.C040020.packed 64 cuts40020 = true := by
 decide +kernel
def pointBounds40020 : List (Nat × Nat × Nat) := [(5249521664,108872720633774,108873106143233)]
theorem point_links_checked40020 : (cuts40020.take 1).map (fun c => (5249433601-1+2*2^10*c.k,108872507281389+c.lower,108872892790724+c.upper)) = pointBounds40020 := by
 decide +kernel
def cuts40021 : List PrefixCut := [⟨60,296561612,296561786⟩,
⟨64,317043465,317043650⟩]
theorem checked40021 : checkPrefixCuts (2^48) 5249564673 10 Manual.Count131072.C040021.packed 64 cuts40021 = true := by
 decide +kernel
def pointBounds40021 : List (Nat × Nat × Nat) := [(5249687552,108873121376970,108873506886666)]
theorem point_links_checked40021 : (cuts40021.take 1).map (fun c => (5249564673-1+2*2^10*c.k,108872824815358+c.lower,108873210324880+c.upper)) = pointBounds40021 := by
 decide +kernel
def cuts40022 : List PrefixCut := [⟨64,318697659,318697846⟩]
theorem checked40022 : checkPrefixCuts (2^48) 5249695745 10 Manual.Count131072.C040022.packed 64 cuts40022 = true := by
 decide +kernel
def cuts40023 : List PrefixCut := [⟨13,64553543,64553580⟩,
⟨64,316169803,316169992⟩]
theorem checked40023 : checkPrefixCuts (2^48) 5249826817 10 Manual.Count131072.C040023.packed 64 cuts40023 = true := by
 decide +kernel
def pointBounds40023 : List (Nat × Nat × Nat) := [(5249853440,108873525110025,108873910619956)]
theorem point_links_checked40023 : (cuts40023.take 1).map (fun c => (5249826817-1+2*2^10*c.k,108873460556482+c.lower,108873846066376+c.upper)) = pointBounds40023 := by
 decide +kernel
def cuts40024 : List PrefixCut := [⟨30,149369685,149369775⟩,
⟨64,316430010,316430201⟩]
theorem checked40024 : checkPrefixCuts (2^48) 5249957889 10 Manual.Count131072.C040024.packed 64 cuts40024 = true := by
 decide +kernel
def pointBounds40024 : List (Nat × Nat × Nat) := [(5250019328,108873926095970,108874311606143)]
theorem point_links_checked40024 : (cuts40024.take 1).map (fun c => (5249957889-1+2*2^10*c.k,108873776726285+c.lower,108874162236368+c.upper)) = pointBounds40024 := by
 decide +kernel
def cuts40025 : List PrefixCut := [⟨47,229516662,229516800⟩,
⟨64,310149406,310149588⟩]
theorem checked40025 : checkPrefixCuts (2^48) 5250088961 10 Manual.Count131072.C040025.packed 64 cuts40025 = true := by
 decide +kernel
def pointBounds40025 : List (Nat × Nat × Nat) := [(5250185216,108874322672957,108874708183369)]
theorem point_links_checked40025 : (cuts40025.take 1).map (fun c => (5250088961-1+2*2^10*c.k,108874093156295+c.lower,108874478666569+c.upper)) = pointBounds40025 := by
 decide +kernel
def cuts40026 : List PrefixCut := [⟨64,318344199,318344386⟩]
theorem checked40026 : checkPrefixCuts (2^48) 5250220033 10 Manual.Count131072.C040026.packed 64 cuts40026 = true := by
 decide +kernel
def pointBounds40026 : List (Nat × Nat × Nat) := [(5250351104,108874721649900,108875107160543)]
theorem point_links_checked40026 : (cuts40026.take 1).map (fun c => (5250220033-1+2*2^10*c.k,108874403305701+c.lower,108874788816157+c.upper)) = pointBounds40026 := by
 decide +kernel
def cuts40027 : List PrefixCut := [⟨64,313189674,313189855⟩]
theorem checked40027 : checkPrefixCuts (2^48) 5250351105 10 Manual.Count131072.C040027.packed 64 cuts40027 = true := by
 decide +kernel
def cuts40028 : List PrefixCut := [⟨17,83576685,83576733⟩,
⟨64,307928231,307928410⟩]
theorem checked40028 : checkPrefixCuts (2^48) 5250482177 10 Manual.Count131072.C040028.packed 64 cuts40028 = true := by
 decide +kernel
def pointBounds40028 : List (Nat × Nat × Nat) := [(5250516992,108875118416259,108875503927131)]
theorem point_links_checked40028 : (cuts40028.take 1).map (fun c => (5250482177-1+2*2^10*c.k,108875034839574+c.lower,108875420350398+c.upper)) = pointBounds40028 := by
 decide +kernel
def cuts40029 : List PrefixCut := [⟨34,166934230,166934330⟩,
⟨64,315425557,315425744⟩]
theorem checked40029 : checkPrefixCuts (2^48) 5250613249 10 Manual.Count131072.C040029.packed 64 cuts40029 = true := by
 decide +kernel
def pointBounds40029 : List (Nat × Nat × Nat) := [(5250682880,108875509702035,108875895213138)]
theorem point_links_checked40029 : (cuts40029.take 1).map (fun c => (5250613249-1+2*2^10*c.k,108875342767805+c.lower,108875728278808+c.upper)) = pointBounds40029 := by
 decide +kernel
def cuts40030 : List PrefixCut := [⟨51,250876716,250876867⟩,
⟨64,316007351,316007541⟩]
theorem checked40030 : checkPrefixCuts (2^48) 5250744321 10 Manual.Count131072.C040030.packed 64 cuts40030 = true := by
 decide +kernel
def pointBounds40030 : List (Nat × Nat × Nat) := [(5250848768,108875909070078,108876294581419)]
theorem point_links_checked40030 : (cuts40030.take 1).map (fun c => (5250744321-1+2*2^10*c.k,108875658193362+c.lower,108876043704552+c.upper)) = pointBounds40030 := by
 decide +kernel
def cuts40031 : List PrefixCut := [⟨64,313158380,313158565⟩]
theorem checked40031 : checkPrefixCuts (2^48) 5250875393 10 Manual.Count131072.C040031.packed 64 cuts40031 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S5.B000000
