import PlattAssemblyKernel
import PlattCertificates.Count131072.C042016
import PlattCertificates.Count131072.C042017
import PlattCertificates.Count131072.C042018
import PlattCertificates.Count131072.C042019
import PlattCertificates.Count131072.C042020
import PlattCertificates.Count131072.C042021
import PlattCertificates.Count131072.C042022
import PlattCertificates.Count131072.C042023
import PlattCertificates.Count131072.C042024
import PlattCertificates.Count131072.C042025
import PlattCertificates.Count131072.C042026
import PlattCertificates.Count131072.C042027
import PlattCertificates.Count131072.C042028
import PlattCertificates.Count131072.C042029
import PlattCertificates.Count131072.C042030
import PlattCertificates.Count131072.C042031
import PlattCertificates.Count131072.C042032
import PlattCertificates.Count131072.C042033
import PlattCertificates.Count131072.C042034
import PlattCertificates.Count131072.C042035
import PlattCertificates.Count131072.C042036
import PlattCertificates.Count131072.C042037
import PlattCertificates.Count131072.C042038
import PlattCertificates.Count131072.C042039
import PlattCertificates.Count131072.C042040
import PlattCertificates.Count131072.C042041
import PlattCertificates.Count131072.C042042
import PlattCertificates.Count131072.C042043
import PlattCertificates.Count131072.C042044
import PlattCertificates.Count131072.C042045
import PlattCertificates.Count131072.C042046
import PlattCertificates.Count131072.C042047
namespace ChenEffective.PlattWindow.Assembly.Prefix.S5.B000063
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts42016 : List PrefixCut := [⟨48,224930563,224930696⟩,
⟨64,298731836,298732011⟩]
theorem checked42016 : checkPrefixCuts (2^48) 5511053313 10 Manual.Count131072.C042016.packed 64 cuts42016 = true := by
 decide +kernel
def pointBounds42016 : List (Nat × Nat × Nat) := [(5511151616,109483692416819,109484078286845)]
theorem point_links_checked42016 : (cuts42016.take 1).map (fun c => (5511053313-1+2*2^10*c.k,109483467486256+c.lower,109483853356149+c.upper)) = pointBounds42016 := by
 decide +kernel
def cuts42017 : List PrefixCut := [⟨64,299286552,299286724⟩]
theorem checked42017 : checkPrefixCuts (2^48) 5511184385 10 Manual.Count131072.C042017.packed 64 cuts42017 = true := by
 decide +kernel
def cuts42018 : List PrefixCut := [⟨5,23033532,23033546⟩,
⟨64,294172274,294172447⟩]
theorem checked42018 : checkPrefixCuts (2^48) 5511315457 10 Manual.Count131072.C042018.packed 64 cuts42018 = true := by
 decide +kernel
def pointBounds42018 : List (Nat × Nat × Nat) := [(5511325696,109484088538176,109484474408430)]
theorem point_links_checked42018 : (cuts42018.take 1).map (fun c => (5511315457-1+2*2^10*c.k,109484065504644+c.lower,109484451374884+c.upper)) = pointBounds42018 := by
 decide +kernel
def cuts42019 : List PrefixCut := [⟨26,120424761,120424831⟩,
⟨64,294420623,294420797⟩]
theorem checked42019 : checkPrefixCuts (2^48) 5511446529 10 Manual.Count131072.C042019.packed 64 cuts42019 = true := by
 decide +kernel
def pointBounds42019 : List (Nat × Nat × Nat) := [(5511499776,109484480101679,109484865972162)]
theorem point_links_checked42019 : (cuts42019.take 1).map (fun c => (5511446529-1+2*2^10*c.k,109484359676918+c.lower,109484745547331+c.upper)) = pointBounds42019 := by
 decide +kernel
def cuts42020 : List PrefixCut := [⟨47,223989991,223990122⟩,
⟨64,303759293,303759470⟩]
theorem checked42020 : checkPrefixCuts (2^48) 5511577601 10 Manual.Count131072.C042020.packed 64 cuts42020 = true := by
 decide +kernel
def pointBounds42020 : List (Nat × Nat × Nat) := [(5511673856,109484878087532,109485263958250)]
theorem point_links_checked42020 : (cuts42020.take 1).map (fun c => (5511577601-1+2*2^10*c.k,109484654097541+c.lower,109485039968128+c.upper)) = pointBounds42020 := by
 decide +kernel
def cuts42021 : List PrefixCut := [⟨64,298543101,298543274⟩]
theorem checked42021 : checkPrefixCuts (2^48) 5511708673 10 Manual.Count131072.C042021.packed 64 cuts42021 = true := by
 decide +kernel
def cuts42022 : List PrefixCut := [⟨4,17720348,17720357⟩,
⟨64,294246411,294246576⟩]
theorem checked42022 : checkPrefixCuts (2^48) 5511839745 10 Manual.Count131072.C042022.packed 64 cuts42022 = true := by
 decide +kernel
def pointBounds42022 : List (Nat × Nat × Nat) := [(5511847936,109485274120283,109485659991229)]
theorem point_links_checked42022 : (cuts42022.take 1).map (fun c => (5511839745-1+2*2^10*c.k,109485256399935+c.lower,109485642270872+c.upper)) = pointBounds42022 := by
 decide +kernel
def cuts42023 : List PrefixCut := [⟨25,117706830,117706899⟩,
⟨64,300673673,300673849⟩]
theorem checked42023 : checkPrefixCuts (2^48) 5511970817 10 Manual.Count131072.C042023.packed 64 cuts42023 = true := by
 decide +kernel
def pointBounds42023 : List (Nat × Nat × Nat) := [(5512022016,109485668353176,109486054224347)]
theorem point_links_checked42023 : (cuts42023.take 1).map (fun c => (5511970817-1+2*2^10*c.k,109485550646346+c.lower,109485936517448+c.upper)) = pointBounds42023 := by
 decide +kernel
def cuts42024 : List PrefixCut := [⟨46,216104792,216104914⟩,
⟨64,302453765,302453936⟩]
theorem checked42024 : checkPrefixCuts (2^48) 5512101889 10 Manual.Count131072.C042024.packed 64 cuts42024 = true := by
 decide +kernel
def pointBounds42024 : List (Nat × Nat × Nat) := [(5512196096,109486067424811,109486453296211)]
theorem point_links_checked42024 : (cuts42024.take 1).map (fun c => (5512101889-1+2*2^10*c.k,109485851320019+c.lower,109486237191297+c.upper)) = pointBounds42024 := by
 decide +kernel
def cuts42025 : List PrefixCut := [⟨64,294940300,294940478⟩]
theorem checked42025 : checkPrefixCuts (2^48) 5512232961 10 Manual.Count131072.C042025.packed 64 cuts42025 = true := by
 decide +kernel
def cuts42026 : List PrefixCut := [⟨3,13071983,13071992⟩,
⟨64,295495003,295495180⟩]
theorem checked42026 : checkPrefixCuts (2^48) 5512364033 10 Manual.Count131072.C042026.packed 64 cuts42026 = true := by
 decide +kernel
def pointBounds42026 : List (Nat × Nat × Nat) := [(5512370176,109486461786067,109486847657703)]
theorem point_links_checked42026 : (cuts42026.take 1).map (fun c => (5512364033-1+2*2^10*c.k,109486448714084+c.lower,109486834585711+c.upper)) = pointBounds42026 := by
 decide +kernel
def cuts42027 : List PrefixCut := [⟨24,111466204,111466268⟩,
⟨64,296100647,296100818⟩]
theorem checked42027 : checkPrefixCuts (2^48) 5512495105 10 Manual.Count131072.C042027.packed 64 cuts42027 = true := by
 decide +kernel
def pointBounds42027 : List (Nat × Nat × Nat) := [(5512544256,109486855675291,109487241547159)]
theorem point_links_checked42027 : (cuts42027.take 1).map (fun c => (5512495105-1+2*2^10*c.k,109486744209087+c.lower,109487130080891+c.upper)) = pointBounds42027 := by
 decide +kernel
def cuts42028 : List PrefixCut := [⟨45,211488904,211489023⟩,
⟨64,299565680,299565851⟩]
theorem checked42028 : checkPrefixCuts (2^48) 5512626177 10 Manual.Count131072.C042028.packed 64 cuts42028 = true := by
 decide +kernel
def pointBounds42028 : List (Nat × Nat × Nat) := [(5512718336,109487251798638,109487637670732)]
theorem point_links_checked42028 : (cuts42028.take 1).map (fun c => (5512626177-1+2*2^10*c.k,109487040309734+c.lower,109487426181709+c.upper)) = pointBounds42028 := by
 decide +kernel
def cuts42029 : List PrefixCut := [⟨64,298537417,298537594⟩]
theorem checked42029 : checkPrefixCuts (2^48) 5512757249 10 Manual.Count131072.C042029.packed 64 cuts42029 = true := by
 decide +kernel
def cuts42030 : List PrefixCut := [⟨2,8832963,8832969⟩,
⟨64,302461670,302461849⟩]
theorem checked42030 : checkPrefixCuts (2^48) 5512888321 10 Manual.Count131072.C042030.packed 64 cuts42030 = true := by
 decide +kernel
def pointBounds42030 : List (Nat × Nat × Nat) := [(5512892416,109487647245794,109488033118123)]
theorem point_links_checked42030 : (cuts42030.take 1).map (fun c => (5512888321-1+2*2^10*c.k,109487638412831+c.lower,109488024285154+c.upper)) = pointBounds42030 := by
 decide +kernel
def cuts42031 : List PrefixCut := [⟨23,105226785,105226846⟩,
⟨64,294234509,294234678⟩]
theorem checked42031 : checkPrefixCuts (2^48) 5513019393 10 Manual.Count131072.C042031.packed 64 cuts42031 = true := by
 decide +kernel
def pointBounds42031 : List (Nat × Nat × Nat) := [(5513066496,109488046101286,109488431973849)]
theorem point_links_checked42031 : (cuts42031.take 1).map (fun c => (5513019393-1+2*2^10*c.k,109487940874501+c.lower,109488326747003+c.upper)) = pointBounds42031 := by
 decide +kernel
def cuts42032 : List PrefixCut := [⟨44,204576448,204576567⟩,
⟨64,296320765,296320939⟩]
theorem checked42032 : checkPrefixCuts (2^48) 5513150465 10 Manual.Count131072.C042032.packed 64 cuts42032 = true := by
 decide +kernel
def pointBounds42032 : List (Nat × Nat × Nat) := [(5513240576,109488439685458,109488825558248)]
theorem point_links_checked42032 : (cuts42032.take 1).map (fun c => (5513150465-1+2*2^10*c.k,109488235109010+c.lower,109488620981681+c.upper)) = pointBounds42032 := by
 decide +kernel
def cuts42033 : List PrefixCut := [⟨64,295394730,295394908⟩]
theorem checked42033 : checkPrefixCuts (2^48) 5513281537 10 Manual.Count131072.C042033.packed 64 cuts42033 = true := by
 decide +kernel
def cuts42034 : List PrefixCut := [⟨1,4901063,4901066⟩,
⟨64,299982430,299982602⟩]
theorem checked42034 : checkPrefixCuts (2^48) 5513412609 10 Manual.Count131072.C042034.packed 64 cuts42034 = true := by
 decide +kernel
def pointBounds42034 : List (Nat × Nat × Nat) := [(5513414656,109488831725568,109489217598594)]
theorem point_links_checked42034 : (cuts42034.take 1).map (fun c => (5513412609-1+2*2^10*c.k,109488826824505+c.lower,109489212697528+c.upper)) = pointBounds42034 := by
 decide +kernel
def cuts42035 : List PrefixCut := [⟨22,102970535,102970595⟩,
⟨64,296146481,296146650⟩]
theorem checked42035 : checkPrefixCuts (2^48) 5513543681 10 Manual.Count131072.C042035.packed 64 cuts42035 = true := by
 decide +kernel
def pointBounds42035 : List (Nat × Nat × Nat) := [(5513588736,109489229777470,109489615650725)]
theorem point_links_checked42035 : (cuts42035.take 1).map (fun c => (5513543681-1+2*2^10*c.k,109489126806935+c.lower,109489512680130+c.upper)) = pointBounds42035 := by
 decide +kernel
def cuts42036 : List PrefixCut := [⟨43,199452034,199452150⟩,
⟨64,300376530,300376706⟩]
theorem checked42036 : checkPrefixCuts (2^48) 5513674753 10 Manual.Count131072.C042036.packed 64 cuts42036 = true := by
 decide +kernel
def pointBounds42036 : List (Nat × Nat × Nat) := [(5513762816,109489622405450,109490008278930)]
theorem point_links_checked42036 : (cuts42036.take 1).map (fun c => (5513674753-1+2*2^10*c.k,109489422953416+c.lower,109489808826780+c.upper)) = pointBounds42036 := by
 decide +kernel
def cuts42037 : List PrefixCut := [⟨64,301390375,301390545⟩]
theorem checked42037 : checkPrefixCuts (2^48) 5513805825 10 Manual.Count131072.C042037.packed 64 cuts42037 = true := by
 decide +kernel
def pointBounds42037 : List (Nat × Nat × Nat) := [(5513936896,109490024720321,109490410594031)]
theorem point_links_checked42037 : (cuts42037.take 1).map (fun c => (5513805825-1+2*2^10*c.k,109489723329946+c.lower,109490109203486+c.upper)) = pointBounds42037 := by
 decide +kernel
def cuts42038 : List PrefixCut := [⟨64,296482667,296482840⟩]
theorem checked42038 : checkPrefixCuts (2^48) 5513936897 10 Manual.Count131072.C042038.packed 64 cuts42038 = true := by
 decide +kernel
def cuts42039 : List PrefixCut := [⟨21,98009248,98009305⟩,
⟨64,298925833,298926007⟩]
theorem checked42039 : checkPrefixCuts (2^48) 5514067969 10 Manual.Count131072.C042039.packed 64 cuts42039 = true := by
 decide +kernel
def pointBounds42039 : List (Nat × Nat × Nat) := [(5514110976,109490419212236,109490805086176)]
theorem point_links_checked42039 : (cuts42039.take 1).map (fun c => (5514067969-1+2*2^10*c.k,109490321202988+c.lower,109490707076871+c.upper)) = pointBounds42039 := by
 decide +kernel
def cuts42040 : List PrefixCut := [⟨42,195043223,195043336⟩,
⟨64,301777204,301777377⟩]
theorem checked42040 : checkPrefixCuts (2^48) 5514199041 10 Manual.Count131072.C042040.packed 64 cuts42040 = true := by
 decide +kernel
def pointBounds42040 : List (Nat × Nat × Nat) := [(5514285056,109490815172044,109491201046214)]
theorem point_links_checked42040 : (cuts42040.take 1).map (fun c => (5514199041-1+2*2^10*c.k,109490620128821+c.lower,109491006002878+c.upper)) = pointBounds42040 := by
 decide +kernel
def cuts42041 : List PrefixCut := [⟨63,293347901,293348068⟩,
⟨64,297482388,297482558⟩]
theorem checked42041 : checkPrefixCuts (2^48) 5514330113 10 Manual.Count131072.C042041.packed 64 cuts42041 = true := by
 decide +kernel
def pointBounds42041 : List (Nat × Nat × Nat) := [(5514459136,109491215253926,109491601128323)]
theorem point_links_checked42041 : (cuts42041.take 1).map (fun c => (5514330113-1+2*2^10*c.k,109490921906025+c.lower,109491307780255+c.upper)) = pointBounds42041 := by
 decide +kernel
def cuts42042 : List PrefixCut := [⟨64,295790911,295791090⟩]
theorem checked42042 : checkPrefixCuts (2^48) 5514461185 10 Manual.Count131072.C042042.packed 64 cuts42042 = true := by
 decide +kernel
def cuts42043 : List PrefixCut := [⟨20,94324954,94325010⟩,
⟨64,299305758,299305938⟩]
theorem checked42043 : checkPrefixCuts (2^48) 5514592257 10 Manual.Count131072.C042043.packed 64 cuts42043 = true := by
 decide +kernel
def pointBounds42043 : List (Nat × Nat × Nat) := [(5514633216,109491609504278,109491995378913)]
theorem point_links_checked42043 : (cuts42043.take 1).map (fun c => (5514592257-1+2*2^10*c.k,109491515179324+c.lower,109491901053903+c.upper)) = pointBounds42043 := by
 decide +kernel
def cuts42044 : List PrefixCut := [⟨41,186398943,186399050⟩,
⟨64,295878944,295879113⟩]
theorem checked42044 : checkPrefixCuts (2^48) 5514723329 10 Manual.Count131072.C042044.packed 64 cuts42044 = true := by
 decide +kernel
def pointBounds42044 : List (Nat × Nat × Nat) := [(5514807296,109492000884025,109492386758891)]
theorem point_links_checked42044 : (cuts42044.take 1).map (fun c => (5514723329-1+2*2^10*c.k,109491814485082+c.lower,109492200359841+c.upper)) = pointBounds42044 := by
 decide +kernel
def cuts42045 : List PrefixCut := [⟨62,290666072,290666242⟩,
⟨64,299495682,299495858⟩]
theorem checked42045 : checkPrefixCuts (2^48) 5514854401 10 Manual.Count131072.C042045.packed 64 cuts42045 = true := by
 decide +kernel
def pointBounds42045 : List (Nat × Nat × Nat) := [(5514981376,109492401030098,109492786905196)]
theorem point_links_checked42045 : (cuts42045.take 1).map (fun c => (5514854401-1+2*2^10*c.k,109492110364026+c.lower,109492496238954+c.upper)) = pointBounds42045 := by
 decide +kernel
def cuts42046 : List PrefixCut := [⟨64,299692702,299692878⟩]
theorem checked42046 : checkPrefixCuts (2^48) 5514985473 10 Manual.Count131072.C042046.packed 64 cuts42046 = true := by
 decide +kernel
def cuts42047 : List PrefixCut := [⟨19,88242628,88242680⟩,
⟨64,295551637,295551814⟩]
theorem checked42047 : checkPrefixCuts (2^48) 5515116545 10 Manual.Count131072.C042047.packed 64 cuts42047 = true := by
 decide +kernel
def pointBounds42047 : List (Nat × Nat × Nat) := [(5515155456,109492797795038,109493183670370)]
theorem point_links_checked42047 : (cuts42047.take 1).map (fun c => (5515116545-1+2*2^10*c.k,109492709552410+c.lower,109493095427690+c.upper)) = pointBounds42047 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S5.B000063
