import PlattAssemblyKernel
import PlattCertificates.Count131072.C045024
import PlattCertificates.Count131072.C045025
import PlattCertificates.Count131072.C045026
import PlattCertificates.Count131072.C045027
import PlattCertificates.Count131072.C045028
import PlattCertificates.Count131072.C045029
import PlattCertificates.Count131072.C045030
import PlattCertificates.Count131072.C045031
import PlattCertificates.Count131072.C045032
import PlattCertificates.Count131072.C045033
import PlattCertificates.Count131072.C045034
import PlattCertificates.Count131072.C045035
import PlattCertificates.Count131072.C045036
import PlattCertificates.Count131072.C045037
import PlattCertificates.Count131072.C045038
import PlattCertificates.Count131072.C045039
import PlattCertificates.Count131072.C045040
import PlattCertificates.Count131072.C045041
import PlattCertificates.Count131072.C045042
import PlattCertificates.Count131072.C045043
import PlattCertificates.Count131072.C045044
import PlattCertificates.Count131072.C045045
import PlattCertificates.Count131072.C045046
import PlattCertificates.Count131072.C045047
import PlattCertificates.Count131072.C045048
import PlattCertificates.Count131072.C045049
import PlattCertificates.Count131072.C045050
import PlattCertificates.Count131072.C045051
import PlattCertificates.Count131072.C045052
import PlattCertificates.Count131072.C045053
import PlattCertificates.Count131072.C045054
import PlattCertificates.Count131072.C045055
namespace ChenEffective.PlattWindow.Assembly.Prefix.S5.B000157
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts45024 : List PrefixCut := [⟨4,17492913,17492923⟩,
⟨64,278310804,278310962⟩]
theorem checked45024 : checkPrefixCuts (2^48) 5905317889 10 Manual.Count131072.C045024.packed 64 cuts45024 = true := by
 decide +kernel
def pointBounds45024 : List (Nat × Nat × Nat) := [(5905326080,110349282741709,110349669114923)]
theorem point_links_checked45024 : (cuts45024.take 1).map (fun c => (5905317889-1+2*2^10*c.k,110349265248796+c.lower,110349651622000+c.upper)) = pointBounds45024 := by
 decide +kernel
def cuts45025 : List PrefixCut := [⟨31,134601246,134601320⟩,
⟨64,278542908,278543063⟩]
theorem checked45025 : checkPrefixCuts (2^48) 5905448961 10 Manual.Count131072.C045025.packed 64 cuts45025 = true := by
 decide +kernel
def pointBounds45025 : List (Nat × Nat × Nat) := [(5905512448,110349678160846,110350064534282)]
theorem point_links_checked45025 : (cuts45025.take 1).map (fun c => (5905448961-1+2*2^10*c.k,110349543559600+c.lower,110349929932962+c.upper)) = pointBounds45025 := by
 decide +kernel
def cuts45026 : List PrefixCut := [⟨58,249749138,249749285⟩,
⟨64,277392822,277392984⟩]
theorem checked45026 : checkPrefixCuts (2^48) 5905580033 10 Manual.Count131072.C045026.packed 64 cuts45026 = true := by
 decide +kernel
def pointBounds45026 : List (Nat × Nat × Nat) := [(5905698816,110350071851646,110350458225310)]
theorem point_links_checked45026 : (cuts45026.take 1).map (fun c => (5905580033-1+2*2^10*c.k,110349822102508+c.lower,110350208476025+c.upper)) = pointBounds45026 := by
 decide +kernel
def cuts45027 : List PrefixCut := [⟨64,280722973,280723136⟩]
theorem checked45027 : checkPrefixCuts (2^48) 5905711105 10 Manual.Count131072.C045027.packed 64 cuts45027 = true := by
 decide +kernel
def cuts45028 : List PrefixCut := [⟨21,92031926,92031979⟩,
⟨64,276332045,276332198⟩]
theorem checked45028 : checkPrefixCuts (2^48) 5905842177 10 Manual.Count131072.C045028.packed 64 cuts45028 = true := by
 decide +kernel
def pointBounds45028 : List (Nat × Nat × Nat) := [(5905885184,110350472250229,110350858624124)]
theorem point_links_checked45028 : (cuts45028.take 1).map (fun c => (5905842177-1+2*2^10*c.k,110350380218303+c.lower,110350766592145+c.upper)) = pointBounds45028 := by
 decide +kernel
def cuts45029 : List PrefixCut := [⟨48,206268002,206268119⟩,
⟨64,277136090,277136249⟩]
theorem checked45029 : checkPrefixCuts (2^48) 5905973249 10 Manual.Count131072.C045029.packed 64 cuts45029 = true := by
 decide +kernel
def pointBounds45029 : List (Nat × Nat × Nat) := [(5906071552,110350862818350,110351249192462)]
theorem point_links_checked45029 : (cuts45029.take 1).map (fun c => (5905973249-1+2*2^10*c.k,110350656550348+c.lower,110351042924343+c.upper)) = pointBounds45029 := by
 decide +kernel
def cuts45030 : List PrefixCut := [⟨64,277177596,277177760⟩]
theorem checked45030 : checkPrefixCuts (2^48) 5906104321 10 Manual.Count131072.C045030.packed 64 cuts45030 = true := by
 decide +kernel
def cuts45031 : List PrefixCut := [⟨11,48991552,48991579⟩,
⟨64,281222267,281222429⟩]
theorem checked45031 : checkPrefixCuts (2^48) 5906235393 10 Manual.Count131072.C045031.packed 64 cuts45031 = true := by
 decide +kernel
def pointBounds45031 : List (Nat × Nat × Nat) := [(5906257920,110351259855586,110351646229931)]
theorem point_links_checked45031 : (cuts45031.take 1).map (fun c => (5906235393-1+2*2^10*c.k,110351210864034+c.lower,110351597238352+c.upper)) = pointBounds45031 := by
 decide +kernel
def cuts45032 : List PrefixCut := [⟨38,165222910,165223004⟩,
⟨64,276355167,276355329⟩]
theorem checked45032 : checkPrefixCuts (2^48) 5906366465 10 Manual.Count131072.C045032.packed 64 cuts45032 = true := by
 decide +kernel
def pointBounds45032 : List (Nat × Nat × Nat) := [(5906444288,110351657309211,110352043683785)]
theorem point_links_checked45032 : (cuts45032.take 1).map (fun c => (5906366465-1+2*2^10*c.k,110351492086301+c.lower,110351878460781+c.upper)) = pointBounds45032 := by
 decide +kernel
def cuts45033 : List PrefixCut := [⟨64,279446604,279446765⟩]
theorem checked45033 : checkPrefixCuts (2^48) 5906497537 10 Manual.Count131072.C045033.packed 64 cuts45033 = true := by
 decide +kernel
def cuts45034 : List PrefixCut := [⟨1,4527136,4527138⟩,
⟨64,276438199,276438358⟩]
theorem checked45034 : checkPrefixCuts (2^48) 5906628609 10 Manual.Count131072.C045034.packed 64 cuts45034 = true := by
 decide +kernel
def pointBounds45034 : List (Nat × Nat × Nat) := [(5906630656,110352052415208,110352438790013)]
theorem point_links_checked45034 : (cuts45034.take 1).map (fun c => (5906628609-1+2*2^10*c.k,110352047888072+c.lower,110352434262875+c.upper)) = pointBounds45034 := by
 decide +kernel
def cuts45035 : List PrefixCut := [⟨28,123563665,123563737⟩,
⟨64,282722173,282722343⟩]
theorem checked45035 : checkPrefixCuts (2^48) 5906759681 10 Manual.Count131072.C045035.packed 64 cuts45035 = true := by
 decide +kernel
def pointBounds45035 : List (Nat × Nat × Nat) := [(5906817024,110352447889936,110352834264970)]
theorem point_links_checked45035 : (cuts45035.take 1).map (fun c => (5906759681-1+2*2^10*c.k,110352324326271+c.lower,110352710701233+c.upper)) = pointBounds45035 := by
 decide +kernel
def cuts45036 : List PrefixCut := [⟨55,238257521,238257655⟩,
⟨64,276950109,276950268⟩]
theorem checked45036 : checkPrefixCuts (2^48) 5906890753 10 Manual.Count131072.C045036.packed 64 cuts45036 = true := by
 decide +kernel
def pointBounds45036 : List (Nat × Nat × Nat) := [(5907003392,110352845305965,110353231681231)]
theorem point_links_checked45036 : (cuts45036.take 1).map (fun c => (5906890753-1+2*2^10*c.k,110352607048444+c.lower,110352993423576+c.upper)) = pointBounds45036 := by
 decide +kernel
def cuts45037 : List PrefixCut := [⟨64,276705679,276705845⟩]
theorem checked45037 : checkPrefixCuts (2^48) 5907021825 10 Manual.Count131072.C045037.packed 64 cuts45037 = true := by
 decide +kernel
def cuts45038 : List PrefixCut := [⟨18,79098493,79098536⟩,
⟨64,278557876,278558037⟩]
theorem checked45038 : checkPrefixCuts (2^48) 5907152897 10 Manual.Count131072.C045038.packed 64 cuts45038 = true := by
 decide +kernel
def pointBounds45038 : List (Nat × Nat × Nat) := [(5907189760,110353239802725,110353626178225)]
theorem point_links_checked45038 : (cuts45038.take 1).map (fun c => (5907152897-1+2*2^10*c.k,110353160704232+c.lower,110353547079689+c.upper)) = pointBounds45038 := by
 decide +kernel
def cuts45039 : List PrefixCut := [⟨45,194357867,194357979⟩,
⟨64,275645159,275645315⟩]
theorem checked45039 : checkPrefixCuts (2^48) 5907283969 10 Manual.Count131072.C045039.packed 64 cuts45039 = true := by
 decide +kernel
def pointBounds45039 : List (Nat × Nat × Nat) := [(5907376128,110353633619975,110354019995705)]
theorem point_links_checked45039 : (cuts45039.take 1).map (fun c => (5907283969-1+2*2^10*c.k,110353439262108+c.lower,110353825637726+c.upper)) = pointBounds45039 := by
 decide +kernel
def cuts45040 : List PrefixCut := [⟨64,275972599,275972759⟩]
theorem checked45040 : checkPrefixCuts (2^48) 5907415041 10 Manual.Count131072.C045040.packed 64 cuts45040 = true := by
 decide +kernel
def cuts45041 : List PrefixCut := [⟨8,34829667,34829688⟩,
⟨64,278729928,278730091⟩]
theorem checked45041 : checkPrefixCuts (2^48) 5907546113 10 Manual.Count131072.C045041.packed 64 cuts45041 = true := by
 decide +kernel
def pointBounds45041 : List (Nat × Nat × Nat) := [(5907562496,110354025709533,110354412085488)]
theorem point_links_checked45041 : (cuts45041.take 1).map (fun c => (5907546113-1+2*2^10*c.k,110353990879866+c.lower,110354377255800+c.upper)) = pointBounds45041 := by
 decide +kernel
def cuts45042 : List PrefixCut := [⟨35,151607418,151607504⟩,
⟨64,279104881,279105044⟩]
theorem checked45042 : checkPrefixCuts (2^48) 5907677185 10 Manual.Count131072.C045042.packed 64 cuts45042 = true := by
 decide +kernel
def pointBounds45042 : List (Nat × Nat × Nat) := [(5907748864,110354421217212,110354807593395)]
theorem point_links_checked45042 : (cuts45042.take 1).map (fun c => (5907677185-1+2*2^10*c.k,110354269609794+c.lower,110354655985891+c.upper)) = pointBounds45042 := by
 decide +kernel
def cuts45043 : List PrefixCut := [⟨62,269331765,269331922⟩,
⟨64,278241102,278241265⟩]
theorem checked45043 : checkPrefixCuts (2^48) 5907808257 10 Manual.Count131072.C045043.packed 64 cuts45043 = true := by
 decide +kernel
def pointBounds45043 : List (Nat × Nat × Nat) := [(5907935232,110354818046440,110355204422857)]
theorem point_links_checked45043 : (cuts45043.take 1).map (fun c => (5907808257-1+2*2^10*c.k,110354548714675+c.lower,110354935090935+c.upper)) = pointBounds45043 := by
 decide +kernel
def cuts45044 : List PrefixCut := [⟨64,281712900,281713060⟩]
theorem checked45044 : checkPrefixCuts (2^48) 5907939329 10 Manual.Count131072.C045044.packed 64 cuts45044 = true := by
 decide +kernel
def cuts45045 : List PrefixCut := [⟨25,110911120,110911186⟩,
⟨64,280658518,280658680⟩]
theorem checked45045 : checkPrefixCuts (2^48) 5908070401 10 Manual.Count131072.C045045.packed 64 cuts45045 = true := by
 decide +kernel
def pointBounds45045 : List (Nat × Nat × Nat) := [(5908121600,110355219579797,110355605956446)]
theorem point_links_checked45045 : (cuts45045.take 1).map (fun c => (5908070401-1+2*2^10*c.k,110355108668677+c.lower,110355495045260+c.upper)) = pointBounds45045 := by
 decide +kernel
def cuts45046 : List PrefixCut := [⟨52,224484168,224484297⟩,
⟨64,277889088,277889247⟩]
theorem checked45046 : checkPrefixCuts (2^48) 5908201473 10 Manual.Count131072.C045046.packed 64 cuts45046 = true := by
 decide +kernel
def pointBounds45046 : List (Nat × Nat × Nat) := [(5908307968,110355613811363,110356000188237)]
theorem point_links_checked45046 : (cuts45046.take 1).map (fun c => (5908201473-1+2*2^10*c.k,110355389327195+c.lower,110355775703940+c.upper)) = pointBounds45046 := by
 decide +kernel
def cuts45047 : List PrefixCut := [⟨64,274452918,274453079⟩]
theorem checked45047 : checkPrefixCuts (2^48) 5908332545 10 Manual.Count131072.C045047.packed 64 cuts45047 = true := by
 decide +kernel
def cuts45048 : List PrefixCut := [⟨15,66266049,66266087⟩,
⟨64,279829964,279830121⟩]
theorem checked45048 : checkPrefixCuts (2^48) 5908463617 10 Manual.Count131072.C045048.packed 64 cuts45048 = true := by
 decide +kernel
def pointBounds45048 : List (Nat × Nat × Nat) := [(5908494336,110356007935250,110356394312353)]
theorem point_links_checked45048 : (cuts45048.take 1).map (fun c => (5908463617-1+2*2^10*c.k,110355941669201+c.lower,110356328046266+c.upper)) = pointBounds45048 := by
 decide +kernel
def cuts45049 : List PrefixCut := [⟨42,183501064,183501173⟩,
⟨64,280014316,280014482⟩]
theorem checked45049 : checkPrefixCuts (2^48) 5908594689 10 Manual.Count131072.C045049.packed 64 cuts45049 = true := by
 decide +kernel
def pointBounds45049 : List (Nat × Nat × Nat) := [(5908680704,110356405000229,110356791377560)]
theorem point_links_checked45049 : (cuts45049.take 1).map (fun c => (5908594689-1+2*2^10*c.k,110356221499165+c.lower,110356607876387+c.upper)) = pointBounds45049 := by
 decide +kernel
def cuts45050 : List PrefixCut := [⟨64,276340094,276340249⟩]
theorem checked45050 : checkPrefixCuts (2^48) 5908725761 10 Manual.Count131072.C045050.packed 64 cuts45050 = true := by
 decide +kernel
def cuts45051 : List PrefixCut := [⟨5,21293319,21293331⟩,
⟨64,279763699,279763864⟩]
theorem checked45051 : checkPrefixCuts (2^48) 5908856833 10 Manual.Count131072.C045051.packed 64 cuts45051 = true := by
 decide +kernel
def pointBounds45051 : List (Nat × Nat × Nat) := [(5908867072,110356799146894,110357185524449)]
theorem point_links_checked45051 : (cuts45051.take 1).map (fun c => (5908856833-1+2*2^10*c.k,110356777853575+c.lower,110357164231118+c.upper)) = pointBounds45051 := by
 decide +kernel
def cuts45052 : List PrefixCut := [⟨32,140189142,140189224⟩,
⟨64,277375775,277375936⟩]
theorem checked45052 : checkPrefixCuts (2^48) 5908987905 10 Manual.Count131072.C045052.packed 64 cuts45052 = true := by
 decide +kernel
def pointBounds45052 : List (Nat × Nat × Nat) := [(5909053440,110357197806416,110357584184206)]
theorem point_links_checked45052 : (cuts45052.take 1).map (fun c => (5908987905-1+2*2^10*c.k,110357057617274+c.lower,110357443994982+c.upper)) = pointBounds45052 := by
 decide +kernel
def cuts45053 : List PrefixCut := [⟨59,254839231,254839377⟩,
⟨64,276464599,276464758⟩]
theorem checked45053 : checkPrefixCuts (2^48) 5909118977 10 Manual.Count131072.C045053.packed 64 cuts45053 = true := by
 decide +kernel
def pointBounds45053 : List (Nat × Nat × Nat) := [(5909239808,110357589832280,110357976210295)]
theorem point_links_checked45053 : (cuts45053.take 1).map (fun c => (5909118977-1+2*2^10*c.k,110357334993049+c.lower,110357721370918+c.upper)) = pointBounds45053 := by
 decide +kernel
def cuts45054 : List PrefixCut := [⟨64,272743127,272743287⟩]
theorem checked45054 : checkPrefixCuts (2^48) 5909250049 10 Manual.Count131072.C045054.packed 64 cuts45054 = true := by
 decide +kernel
def cuts45055 : List PrefixCut := [⟨22,96692330,96692387⟩,
⟨64,279500725,279500885⟩]
theorem checked45055 : checkPrefixCuts (2^48) 5909381121 10 Manual.Count131072.C045055.packed 64 cuts45055 = true := by
 decide +kernel
def pointBounds45055 : List (Nat × Nat × Nat) := [(5909426176,110357980893105,110358367271350)]
theorem point_links_checked45055 : (cuts45055.take 1).map (fun c => (5909381121-1+2*2^10*c.k,110357884200775+c.lower,110358270578963+c.upper)) = pointBounds45055 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S5.B000157
