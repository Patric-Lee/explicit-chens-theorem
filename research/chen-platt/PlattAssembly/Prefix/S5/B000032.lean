import PlattAssemblyKernel
import PlattCertificates.Count131072.C041024
import PlattCertificates.Count131072.C041025
import PlattCertificates.Count131072.C041026
import PlattCertificates.Count131072.C041027
import PlattCertificates.Count131072.C041028
import PlattCertificates.Count131072.C041029
import PlattCertificates.Count131072.C041030
import PlattCertificates.Count131072.C041031
import PlattCertificates.Count131072.C041032
import PlattCertificates.Count131072.C041033
import PlattCertificates.Count131072.C041034
import PlattCertificates.Count131072.C041035
import PlattCertificates.Count131072.C041036
import PlattCertificates.Count131072.C041037
import PlattCertificates.Count131072.C041038
import PlattCertificates.Count131072.C041039
import PlattCertificates.Count131072.C041040
import PlattCertificates.Count131072.C041041
import PlattCertificates.Count131072.C041042
import PlattCertificates.Count131072.C041043
import PlattCertificates.Count131072.C041044
import PlattCertificates.Count131072.C041045
import PlattCertificates.Count131072.C041046
import PlattCertificates.Count131072.C041047
import PlattCertificates.Count131072.C041048
import PlattCertificates.Count131072.C041049
import PlattCertificates.Count131072.C041050
import PlattCertificates.Count131072.C041051
import PlattCertificates.Count131072.C041052
import PlattCertificates.Count131072.C041053
import PlattCertificates.Count131072.C041054
import PlattCertificates.Count131072.C041055
namespace ChenEffective.PlattWindow.Assembly.Prefix.S5.B000032
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts41024 : List PrefixCut := [⟨6,29763640,29763656⟩,
⟨64,304956219,304956403⟩]
theorem checked41024 : checkPrefixCuts (2^48) 5381029889 10 Manual.Count131072.C041024.packed 64 cuts41024 = true := by
 decide +kernel
def pointBounds41024 : List (Nat × Nat × Nat) := [(5381042176,109183752018088,109184137711704)]
theorem point_links_checked41024 : (cuts41024.take 1).map (fun c => (5381029889-1+2*2^10*c.k,109183722254448+c.lower,109184107948048+c.upper)) = pointBounds41024 := by
 decide +kernel
def cuts41025 : List PrefixCut := [⟨25,119888141,119888212⟩,
⟨64,304582669,304582848⟩]
theorem checked41025 : checkPrefixCuts (2^48) 5381160961 10 Manual.Count131072.C041025.packed 64 cuts41025 = true := by
 decide +kernel
def pointBounds41025 : List (Nat × Nat × Nat) := [(5381212160,109184147098808,109184532792663)]
theorem point_links_checked41025 : (cuts41025.take 1).map (fun c => (5381160961-1+2*2^10*c.k,109184027210667+c.lower,109184412904451+c.upper)) = pointBounds41025 := by
 decide +kernel
def cuts41026 : List PrefixCut := [⟨44,211681396,211681517⟩,
⟨64,306458270,306458448⟩]
theorem checked41026 : checkPrefixCuts (2^48) 5381292033 10 Manual.Count131072.C041026.packed 64 cuts41026 = true := by
 decide +kernel
def pointBounds41026 : List (Nat × Nat × Nat) := [(5381382144,109184543474732,109184929168816)]
theorem point_links_checked41026 : (cuts41026.take 1).map (fun c => (5381292033-1+2*2^10*c.k,109184331793336+c.lower,109184717487299+c.upper)) = pointBounds41026 := by
 decide +kernel
def cuts41027 : List PrefixCut := [⟨63,300174293,300174471⟩,
⟨64,304829318,304829499⟩]
theorem checked41027 : checkPrefixCuts (2^48) 5381423105 10 Manual.Count131072.C041027.packed 64 cuts41027 = true := by
 decide +kernel
def pointBounds41027 : List (Nat × Nat × Nat) := [(5381552128,109184938425899,109185324120218)]
theorem point_links_checked41027 : (cuts41027.take 1).map (fun c => (5381423105-1+2*2^10*c.k,109184638251606+c.lower,109185023945747+c.upper)) = pointBounds41027 := by
 decide +kernel
def cuts41028 : List PrefixCut := [⟨64,308169313,308169498⟩]
theorem checked41028 : checkPrefixCuts (2^48) 5381554177 10 Manual.Count131072.C041028.packed 64 cuts41028 = true := by
 decide +kernel
def cuts41029 : List PrefixCut := [⟨18,86873943,86873996⟩,
⟨64,305128343,305128519⟩]
theorem checked41029 : checkPrefixCuts (2^48) 5381685249 10 Manual.Count131072.C041029.packed 64 cuts41029 = true := by
 decide +kernel
def pointBounds41029 : List (Nat × Nat × Nat) := [(5381722112,109185338124180,109185723818740)]
theorem point_links_checked41029 : (cuts41029.take 1).map (fun c => (5381685249-1+2*2^10*c.k,109185251250237+c.lower,109185636944744+c.upper)) = pointBounds41029 := by
 decide +kernel
def cuts41030 : List PrefixCut := [⟨37,175259751,175259855⟩,
⟨64,306323773,306323956⟩]
theorem checked41030 : checkPrefixCuts (2^48) 5381816321 10 Manual.Count131072.C041030.packed 64 cuts41030 = true := by
 decide +kernel
def pointBounds41030 : List (Nat × Nat × Nat) := [(5381892096,109185731638331,109186117333118)]
theorem point_links_checked41030 : (cuts41030.take 1).map (fun c => (5381816321-1+2*2^10*c.k,109185556378580+c.lower,109185942073263+c.upper)) = pointBounds41030 := by
 decide +kernel
def cuts41031 : List PrefixCut := [⟨56,264529693,264529854⟩,
⟨64,303492172,303492356⟩]
theorem checked41031 : checkPrefixCuts (2^48) 5381947393 10 Manual.Count131072.C041031.packed 64 cuts41031 = true := by
 decide +kernel
def pointBounds41031 : List (Nat × Nat × Nat) := [(5382062080,109186127232046,109186512927073)]
theorem point_links_checked41031 : (cuts41031.take 1).map (fun c => (5381947393-1+2*2^10*c.k,109185862702353+c.lower,109186248397219+c.upper)) = pointBounds41031 := by
 decide +kernel
def cuts41032 : List PrefixCut := [⟨64,304896815,304896995⟩]
theorem checked41032 : checkPrefixCuts (2^48) 5382078465 10 Manual.Count131072.C041032.packed 64 cuts41032 = true := by
 decide +kernel
def cuts41033 : List PrefixCut := [⟨11,51721897,51721926⟩,
⟨64,303006704,303006881⟩]
theorem checked41033 : checkPrefixCuts (2^48) 5382209537 10 Manual.Count131072.C041033.packed 64 cuts41033 = true := by
 decide +kernel
def pointBounds41033 : List (Nat × Nat × Nat) := [(5382232064,109186522813237,109186908508496)]
theorem point_links_checked41033 : (cuts41033.take 1).map (fun c => (5382209537-1+2*2^10*c.k,109186471091340+c.lower,109186856786570+c.upper)) = pointBounds41033 := by
 decide +kernel
def cuts41034 : List PrefixCut := [⟨30,143185636,143185716⟩,
⟨64,307496726,307496903⟩]
theorem checked41034 : checkPrefixCuts (2^48) 5382340609 10 Manual.Count131072.C041034.packed 64 cuts41034 = true := by
 decide +kernel
def pointBounds41034 : List (Nat × Nat × Nat) := [(5382402048,109186917283680,109187302979167)]
theorem point_links_checked41034 : (cuts41034.take 1).map (fun c => (5382340609-1+2*2^10*c.k,109186774098044+c.lower,109187159793451+c.upper)) = pointBounds41034 := by
 decide +kernel
def cuts41035 : List PrefixCut := [⟨49,233546075,233546217⟩,
⟨64,304926843,304927026⟩]
theorem checked41035 : checkPrefixCuts (2^48) 5382471681 10 Manual.Count131072.C041035.packed 64 cuts41035 = true := by
 decide +kernel
def pointBounds41035 : List (Nat × Nat × Nat) := [(5382572032,109187315140845,109187700836571)]
theorem point_links_checked41035 : (cuts41035.take 1).map (fun c => (5382471681-1+2*2^10*c.k,109187081594770+c.lower,109187467290354+c.upper)) = pointBounds41035 := by
 decide +kernel
def cuts41036 : List PrefixCut := [⟨64,308945994,308946176⟩]
theorem checked41036 : checkPrefixCuts (2^48) 5382602753 10 Manual.Count131072.C041036.packed 64 cuts41036 = true := by
 decide +kernel
def cuts41037 : List PrefixCut := [⟨4,19243508,19243520⟩,
⟨64,306585331,306585512⟩]
theorem checked41037 : checkPrefixCuts (2^48) 5382733825 10 Manual.Count131072.C041037.packed 64 cuts41037 = true := by
 decide +kernel
def pointBounds41037 : List (Nat × Nat × Nat) := [(5382742016,109187714711115,109188100407076)]
theorem point_links_checked41037 : (cuts41037.take 1).map (fun c => (5382733825-1+2*2^10*c.k,109187695467607+c.lower,109188081163556+c.upper)) = pointBounds41037 := by
 decide +kernel
def cuts41038 : List PrefixCut := [⟨23,112372669,112372733⟩,
⟨64,309558423,309558599⟩]
theorem checked41038 : checkPrefixCuts (2^48) 5382864897 10 Manual.Count131072.C041038.packed 64 cuts41038 = true := by
 decide +kernel
def pointBounds41038 : List (Nat × Nat × Nat) := [(5382912000,109188114425607,109188500121801)]
theorem point_links_checked41038 : (cuts41038.take 1).map (fun c => (5382864897-1+2*2^10*c.k,109188002052938+c.lower,109188387749068+c.upper)) = pointBounds41038 := by
 decide +kernel
def cuts41039 : List PrefixCut := [⟨42,204450843,204450964⟩,
⟨64,307720788,307720969⟩]
theorem checked41039 : checkPrefixCuts (2^48) 5382995969 10 Manual.Count131072.C041039.packed 64 cuts41039 = true := by
 decide +kernel
def pointBounds41039 : List (Nat × Nat × Nat) := [(5383081984,109188516062204,109188901758631)]
theorem point_links_checked41039 : (cuts41039.take 1).map (fun c => (5382995969-1+2*2^10*c.k,109188311611361+c.lower,109188697307667+c.upper)) = pointBounds41039 := by
 decide +kernel
def cuts41040 : List PrefixCut := [⟨61,292968303,292968477⟩,
⟨64,307556409,307556592⟩]
theorem checked41040 : checkPrefixCuts (2^48) 5383127041 10 Manual.Count131072.C041040.packed 64 cuts41040 = true := by
 decide +kernel
def pointBounds41040 : List (Nat × Nat × Nat) := [(5383251968,109188912300452,109189297997113)]
theorem point_links_checked41040 : (cuts41040.take 1).map (fun c => (5383127041-1+2*2^10*c.k,109188619332149+c.lower,109189005028636+c.upper)) = pointBounds41040 := by
 decide +kernel
def cuts41041 : List PrefixCut := [⟨64,305195994,305196168⟩]
theorem checked41041 : checkPrefixCuts (2^48) 5383258113 10 Manual.Count131072.C041041.packed 64 cuts41041 = true := by
 decide +kernel
def cuts41042 : List PrefixCut := [⟨16,76755344,76755391⟩,
⟨64,307070854,307071035⟩]
theorem checked41042 : checkPrefixCuts (2^48) 5383389185 10 Manual.Count131072.C041042.packed 64 cuts41042 = true := by
 decide +kernel
def pointBounds41042 : List (Nat × Nat × Nat) := [(5383421952,109189308839896,109189694536787)]
theorem point_links_checked41042 : (cuts41042.take 1).map (fun c => (5383389185-1+2*2^10*c.k,109189232084552+c.lower,109189617781396+c.upper)) = pointBounds41042 := by
 decide +kernel
def cuts41043 : List PrefixCut := [⟨35,165322625,165322725⟩,
⟨64,303194369,303194553⟩]
theorem checked41043 : checkPrefixCuts (2^48) 5383520257 10 Manual.Count131072.C041043.packed 64 cuts41043 = true := by
 decide +kernel
def pointBounds41043 : List (Nat × Nat × Nat) := [(5383591936,109189704478031,109190090175156)]
theorem point_links_checked41043 : (cuts41043.take 1).map (fun c => (5383520257-1+2*2^10*c.k,109189539155406+c.lower,109189924852431+c.upper)) = pointBounds41043 := by
 decide +kernel
def cuts41044 : List PrefixCut := [⟨54,257335613,257335764⟩,
⟨64,304232654,304232831⟩]
theorem checked41044 : checkPrefixCuts (2^48) 5383651329 10 Manual.Count131072.C041044.packed 64 cuts41044 = true := by
 decide +kernel
def pointBounds41044 : List (Nat × Nat × Nat) := [(5383761920,109190099685388,109190485382748)]
theorem point_links_checked41044 : (cuts41044.take 1).map (fun c => (5383651329-1+2*2^10*c.k,109189842349775+c.lower,109190228046984+c.upper)) = pointBounds41044 := by
 decide +kernel
def cuts41045 : List PrefixCut := [⟨64,304904878,304905058⟩]
theorem checked41045 : checkPrefixCuts (2^48) 5383782401 10 Manual.Count131072.C041045.packed 64 cuts41045 = true := by
 decide +kernel
def cuts41046 : List PrefixCut := [⟨9,43811171,43811196⟩,
⟨64,306256750,306256930⟩]
theorem checked41046 : checkPrefixCuts (2^48) 5383913473 10 Manual.Count131072.C041046.packed 64 cuts41046 = true := by
 decide +kernel
def pointBounds41046 : List (Nat × Nat × Nat) := [(5383931904,109190495298478,109190880996069)]
theorem point_links_checked41046 : (cuts41046.take 1).map (fun c => (5383913473-1+2*2^10*c.k,109190451487307+c.lower,109190837184873+c.upper)) = pointBounds41046 := by
 decide +kernel
def cuts41047 : List PrefixCut := [⟨28,138748918,138748995⟩,
⟨64,309072384,309072562⟩]
theorem checked41047 : checkPrefixCuts (2^48) 5384044545 10 Manual.Count131072.C041047.packed 64 cuts41047 = true := by
 decide +kernel
def pointBounds41047 : List (Nat × Nat × Nat) := [(5384101888,109190896492975,109191282190798)]
theorem point_links_checked41047 : (cuts41047.take 1).map (fun c => (5384044545-1+2*2^10*c.k,109190757744057+c.lower,109191143441803+c.upper)) = pointBounds41047 := by
 decide +kernel
def cuts41048 : List PrefixCut := [⟨47,225264658,225264789⟩,
⟨64,306189569,306189747⟩]
theorem checked41048 : checkPrefixCuts (2^48) 5384175617 10 Manual.Count131072.C041048.packed 64 cuts41048 = true := by
 decide +kernel
def pointBounds41048 : List (Nat × Nat × Nat) := [(5384271872,109191292081099,109191677779154)]
theorem point_links_checked41048 : (cuts41048.take 1).map (fun c => (5384175617-1+2*2^10*c.k,109191066816441+c.lower,109191452514365+c.upper)) = pointBounds41048 := by
 decide +kernel
def cuts41049 : List PrefixCut := [⟨64,306704876,306705055⟩]
theorem checked41049 : checkPrefixCuts (2^48) 5384306689 10 Manual.Count131072.C041049.packed 64 cuts41049 = true := by
 decide +kernel
def cuts41050 : List PrefixCut := [⟨2,8991406,8991410⟩,
⟨64,305547375,305547557⟩]
theorem checked41050 : checkPrefixCuts (2^48) 5384437761 10 Manual.Count131072.C041050.packed 64 cuts41050 = true := by
 decide +kernel
def pointBounds41050 : List (Nat × Nat × Nat) := [(5384441856,109191688702292,109192074400577)]
theorem point_links_checked41050 : (cuts41050.take 1).map (fun c => (5384437761-1+2*2^10*c.k,109191679710886+c.lower,109192065409167+c.upper)) = pointBounds41050 := by
 decide +kernel
def cuts41051 : List PrefixCut := [⟨21,101568675,101568736⟩,
⟨64,307630861,307631043⟩]
theorem checked41051 : checkPrefixCuts (2^48) 5384568833 10 Manual.Count131072.C041051.packed 64 cuts41051 = true := by
 decide +kernel
def pointBounds41051 : List (Nat × Nat × Nat) := [(5384611840,109192086826936,109192472525460)]
theorem point_links_checked41051 : (cuts41051.take 1).map (fun c => (5384568833-1+2*2^10*c.k,109191985258261+c.lower,109192370956724+c.upper)) = pointBounds41051 := by
 decide +kernel
def cuts41052 : List PrefixCut := [⟨40,190586209,190586320⟩,
⟨64,306734706,306734888⟩]
theorem checked41052 : checkPrefixCuts (2^48) 5384699905 10 Manual.Count131072.C041052.packed 64 cuts41052 = true := by
 decide +kernel
def pointBounds41052 : List (Nat × Nat × Nat) := [(5384781824,109192483475331,109192869174087)]
theorem point_links_checked41052 : (cuts41052.take 1).map (fun c => (5384699905-1+2*2^10*c.k,109192292889122+c.lower,109192678587767+c.upper)) = pointBounds41052 := by
 decide +kernel
def cuts41053 : List PrefixCut := [⟨59,279076129,279076291⟩,
⟨64,303591037,303591214⟩]
theorem checked41053 : checkPrefixCuts (2^48) 5384830977 10 Manual.Count131072.C041053.packed 64 cuts41053 = true := by
 decide +kernel
def pointBounds41053 : List (Nat × Nat × Nat) := [(5384951808,109192878699957,109193264398946)]
theorem point_links_checked41053 : (cuts41053.take 1).map (fun c => (5384830977-1+2*2^10*c.k,109192599623828+c.lower,109192985322655+c.upper)) = pointBounds41053 := by
 decide +kernel
def cuts41054 : List PrefixCut := [⟨64,299506549,299506726⟩]
theorem checked41054 : checkPrefixCuts (2^48) 5384962049 10 Manual.Count131072.C041054.packed 64 cuts41054 = true := by
 decide +kernel
def cuts41055 : List PrefixCut := [⟨14,66329528,66329567⟩,
⟨64,304935216,304935392⟩]
theorem checked41055 : checkPrefixCuts (2^48) 5385093121 10 Manual.Count131072.C041055.packed 64 cuts41055 = true := by
 decide +kernel
def pointBounds41055 : List (Nat × Nat × Nat) := [(5385121792,109193269050942,109193654750162)]
theorem point_links_checked41055 : (cuts41055.take 1).map (fun c => (5385093121-1+2*2^10*c.k,109193202721414+c.lower,109193588420595+c.upper)) = pointBounds41055 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S5.B000032
