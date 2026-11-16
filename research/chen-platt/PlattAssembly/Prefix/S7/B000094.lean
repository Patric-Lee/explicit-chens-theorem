import PlattAssemblyKernel
import PlattCertificates.Count131072.C063008
import PlattCertificates.Count131072.C063009
import PlattCertificates.Count131072.C063010
import PlattCertificates.Count131072.C063011
import PlattCertificates.Count131072.C063012
import PlattCertificates.Count131072.C063013
import PlattCertificates.Count131072.C063014
import PlattCertificates.Count131072.C063015
import PlattCertificates.Count131072.C063016
import PlattCertificates.Count131072.C063017
import PlattCertificates.Count131072.C063018
import PlattCertificates.Count131072.C063019
import PlattCertificates.Count131072.C063020
import PlattCertificates.Count131072.C063021
import PlattCertificates.Count131072.C063022
import PlattCertificates.Count131072.C063023
import PlattCertificates.Count131072.C063024
import PlattCertificates.Count131072.C063025
import PlattCertificates.Count131072.C063026
import PlattCertificates.Count131072.C063027
import PlattCertificates.Count131072.C063028
import PlattCertificates.Count131072.C063029
import PlattCertificates.Count131072.C063030
import PlattCertificates.Count131072.C063031
import PlattCertificates.Count131072.C063032
import PlattCertificates.Count131072.C063033
import PlattCertificates.Count131072.C063034
import PlattCertificates.Count131072.C063035
import PlattCertificates.Count131072.C063036
import PlattCertificates.Count131072.C063037
import PlattCertificates.Count131072.C063038
import PlattCertificates.Count131072.C063039
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000094
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts63008 : List PrefixCut := [⟨25,77705411,77705453⟩,
⟨64,196527997,196528106⟩]
theorem checked63008 : checkPrefixCuts (2^48) 8262516737 10 Manual.Count131072.C063008.packed 64 cuts63008 = true := by
 decide +kernel
def pointBounds63008 : List (Nat × Nat × Nat) := [(8262567936,114520252646545,114520641399647)]
theorem point_links_checked63008 : (cuts63008.take 1).map (fun c => (8262516737-1+2*2^10*c.k,114520174941134+c.lower,114520563694194+c.upper)) = pointBounds63008 := by
 decide +kernel
def cuts63009 : List PrefixCut := [⟨64,196116072,196116190⟩]
theorem checked63009 : checkPrefixCuts (2^48) 8262647809 10 Manual.Count131072.C063009.packed 64 cuts63009 = true := by
 decide +kernel
def cuts63010 : List PrefixCut := [⟨24,72286571,72286615⟩,
⟨64,195772312,195772427⟩]
theorem checked63010 : checkPrefixCuts (2^48) 8262778881 10 Manual.Count131072.C063010.packed 64 cuts63010 = true := by
 decide +kernel
def pointBounds63010 : List (Nat × Nat × Nat) := [(8262828032,114520639871774,114521028625105)]
theorem point_links_checked63010 : (cuts63010.take 1).map (fun c => (8262778881-1+2*2^10*c.k,114520567585203+c.lower,114520956338490+c.upper)) = pointBounds63010 := by
 decide +kernel
def cuts63011 : List PrefixCut := [⟨64,195530761,195530871⟩]
theorem checked63011 : checkPrefixCuts (2^48) 8262909953 10 Manual.Count131072.C063011.packed 64 cuts63011 = true := by
 decide +kernel
def cuts63012 : List PrefixCut := [⟨23,70342623,70342665⟩,
⟨64,194301356,194301469⟩]
theorem checked63012 : checkPrefixCuts (2^48) 8263041025 10 Manual.Count131072.C063012.packed 64 cuts63012 = true := by
 decide +kernel
def pointBounds63012 : List (Nat × Nat × Nat) := [(8263088128,114521029230899,114521417984453)]
theorem point_links_checked63012 : (cuts63012.take 1).map (fun c => (8263041025-1+2*2^10*c.k,114520958888276+c.lower,114521347641788+c.upper)) = pointBounds63012 := by
 decide +kernel
def cuts63013 : List PrefixCut := [⟨64,195183937,195184047⟩]
theorem checked63013 : checkPrefixCuts (2^48) 8263172097 10 Manual.Count131072.C063013.packed 64 cuts63013 = true := by
 decide +kernel
def cuts63014 : List PrefixCut := [⟨22,68058175,68058213⟩,
⟨64,194772089,194772201⟩]
theorem checked63014 : checkPrefixCuts (2^48) 8263303169 10 Manual.Count131072.C063014.packed 64 cuts63014 = true := by
 decide +kernel
def pointBounds63014 : List (Nat × Nat × Nat) := [(8263348224,114521416431744,114521805185517)]
theorem point_links_checked63014 : (cuts63014.take 1).map (fun c => (8263303169-1+2*2^10*c.k,114521348373569+c.lower,114521737127304+c.upper)) = pointBounds63014 := by
 decide +kernel
def cuts63015 : List PrefixCut := [⟨64,194394301,194394408⟩]
theorem checked63015 : checkPrefixCuts (2^48) 8263434241 10 Manual.Count131072.C063015.packed 64 cuts63015 = true := by
 decide +kernel
def cuts63016 : List PrefixCut := [⟨21,63934511,63934548⟩,
⟨64,193846233,193846345⟩]
theorem checked63016 : checkPrefixCuts (2^48) 8263565313 10 Manual.Count131072.C063016.packed 64 cuts63016 = true := by
 decide +kernel
def pointBounds63016 : List (Nat × Nat × Nat) := [(8263608320,114521801474470,114522190228461)]
theorem point_links_checked63016 : (cuts63016.take 1).map (fun c => (8263565313-1+2*2^10*c.k,114521737539959+c.lower,114522126293913+c.upper)) = pointBounds63016 := by
 decide +kernel
def cuts63017 : List PrefixCut := [⟨64,195341843,195341953⟩]
theorem checked63017 : checkPrefixCuts (2^48) 8263696385 10 Manual.Count131072.C063017.packed 64 cuts63017 = true := by
 decide +kernel
def cuts63018 : List PrefixCut := [⟨20,60594512,60594548⟩,
⟨64,195543112,195543223⟩]
theorem checked63018 : checkPrefixCuts (2^48) 8263827457 10 Manual.Count131072.C063018.packed 64 cuts63018 = true := by
 decide +kernel
def pointBounds63018 : List (Nat × Nat × Nat) := [(8263868416,114522187322547,114522576076759)]
theorem point_links_checked63018 : (cuts63018.take 1).map (fun c => (8263827457-1+2*2^10*c.k,114522126728035+c.lower,114522515482211+c.upper)) = pointBounds63018 := by
 decide +kernel
def cuts63019 : List PrefixCut := [⟨64,196527778,196527891⟩]
theorem checked63019 : checkPrefixCuts (2^48) 8263958529 10 Manual.Count131072.C063019.packed 64 cuts63019 = true := by
 decide +kernel
def cuts63020 : List PrefixCut := [⟨19,55245189,55245221⟩,
⟨64,195230360,195230473⟩]
theorem checked63020 : checkPrefixCuts (2^48) 8264089601 10 Manual.Count131072.C063020.packed 64 cuts63020 = true := by
 decide +kernel
def pointBounds63020 : List (Nat × Nat × Nat) := [(8264128512,114522574044114,114522962798546)]
theorem point_links_checked63020 : (cuts63020.take 1).map (fun c => (8264089601-1+2*2^10*c.k,114522518798925+c.lower,114522907553325+c.upper)) = pointBounds63020 := by
 decide +kernel
def cuts63021 : List PrefixCut := [⟨64,196112813,196112931⟩]
theorem checked63021 : checkPrefixCuts (2^48) 8264220673 10 Manual.Count131072.C063021.packed 64 cuts63021 = true := by
 decide +kernel
def cuts63022 : List PrefixCut := [⟨18,53915149,53915182⟩,
⟨64,191852369,191852483⟩]
theorem checked63022 : checkPrefixCuts (2^48) 8264351745 10 Manual.Count131072.C063022.packed 64 cuts63022 = true := by
 decide +kernel
def pointBounds63022 : List (Nat × Nat × Nat) := [(8264388608,114522964057247,114523352811911)]
theorem point_links_checked63022 : (cuts63022.take 1).map (fun c => (8264351745-1+2*2^10*c.k,114522910142098+c.lower,114523298896729+c.upper)) = pointBounds63022 := by
 decide +kernel
def cuts63023 : List PrefixCut := [⟨64,196481242,196481355⟩]
theorem checked63023 : checkPrefixCuts (2^48) 8264482817 10 Manual.Count131072.C063023.packed 64 cuts63023 = true := by
 decide +kernel
def cuts63024 : List PrefixCut := [⟨17,51393172,51393201⟩,
⟨64,194775242,194775354⟩]
theorem checked63024 : checkPrefixCuts (2^48) 8264613889 10 Manual.Count131072.C063024.packed 64 cuts63024 = true := by
 decide +kernel
def pointBounds63024 : List (Nat × Nat × Nat) := [(8264648704,114523349868881,114523738623768)]
theorem point_links_checked63024 : (cuts63024.take 1).map (fun c => (8264613889-1+2*2^10*c.k,114523298475709+c.lower,114523687230567+c.upper)) = pointBounds63024 := by
 decide +kernel
def cuts63025 : List PrefixCut := [⟨64,196611236,196611347⟩]
theorem checked63025 : checkPrefixCuts (2^48) 8264744961 10 Manual.Count131072.C063025.packed 64 cuts63025 = true := by
 decide +kernel
def cuts63026 : List PrefixCut := [⟨16,48803238,48803267⟩,
⟨64,195995096,195995207⟩]
theorem checked63026 : checkPrefixCuts (2^48) 8264876033 10 Manual.Count131072.C063026.packed 64 cuts63026 = true := by
 decide +kernel
def pointBounds63026 : List (Nat × Nat × Nat) := [(8264908800,114523738665425,114524127420535)]
theorem point_links_checked63026 : (cuts63026.take 1).map (fun c => (8264876033-1+2*2^10*c.k,114523689862187+c.lower,114524078617268+c.upper)) = pointBounds63026 := by
 decide +kernel
def cuts63027 : List PrefixCut := [⟨64,194050794,194050912⟩]
theorem checked63027 : checkPrefixCuts (2^48) 8265007105 10 Manual.Count131072.C063027.packed 64 cuts63027 = true := by
 decide +kernel
def cuts63028 : List PrefixCut := [⟨15,44510690,44510715⟩,
⟨64,194967202,194967313⟩]
theorem checked63028 : checkPrefixCuts (2^48) 8265138177 10 Manual.Count131072.C063028.packed 64 cuts63028 = true := by
 decide +kernel
def pointBounds63028 : List (Nat × Nat × Nat) := [(8265168896,114524124418767,114524513174102)]
theorem point_links_checked63028 : (cuts63028.take 1).map (fun c => (8265138177-1+2*2^10*c.k,114524079908077+c.lower,114524468663387+c.upper)) = pointBounds63028 := by
 decide +kernel
def cuts63029 : List PrefixCut := [⟨64,193431650,193431760⟩]
theorem checked63029 : checkPrefixCuts (2^48) 8265269249 10 Manual.Count131072.C063029.packed 64 cuts63029 = true := by
 decide +kernel
def cuts63030 : List PrefixCut := [⟨14,43623866,43623892⟩,
⟨64,197651337,197651454⟩]
theorem checked63030 : checkPrefixCuts (2^48) 8265400321 10 Manual.Count131072.C063030.packed 64 cuts63030 = true := by
 decide +kernel
def pointBounds63030 : List (Nat × Nat × Nat) := [(8265428992,114524511930795,114524900686352)]
theorem point_links_checked63030 : (cuts63030.take 1).map (fun c => (8265400321-1+2*2^10*c.k,114524468306929+c.lower,114524857062460+c.upper)) = pointBounds63030 := by
 decide +kernel
def cuts63031 : List PrefixCut := [⟨64,194685517,194685626⟩]
theorem checked63031 : checkPrefixCuts (2^48) 8265531393 10 Manual.Count131072.C063031.packed 64 cuts63031 = true := by
 decide +kernel
def cuts63032 : List PrefixCut := [⟨13,39502018,39502042⟩,
⟨64,201254695,201254809⟩]
theorem checked63032 : checkPrefixCuts (2^48) 8265662465 10 Manual.Count131072.C063032.packed 64 cuts63032 = true := by
 decide +kernel
def pointBounds63032 : List (Nat × Nat × Nat) := [(8265689088,114524900145801,114525288901582)]
theorem point_links_checked63032 : (cuts63032.take 1).map (fun c => (8265662465-1+2*2^10*c.k,114524860643783+c.lower,114525249399540+c.upper)) = pointBounds63032 := by
 decide +kernel
def cuts63033 : List PrefixCut := [⟨64,194883648,194883760⟩]
theorem checked63033 : checkPrefixCuts (2^48) 8265793537 10 Manual.Count131072.C063033.packed 64 cuts63033 = true := by
 decide +kernel
def cuts63034 : List PrefixCut := [⟨12,36027427,36027447⟩,
⟨64,197706884,197706996⟩]
theorem checked63034 : checkPrefixCuts (2^48) 8265924609 10 Manual.Count131072.C063034.packed 64 cuts63034 = true := by
 decide +kernel
def pointBounds63034 : List (Nat × Nat × Nat) := [(8265949184,114525292809553,114525681565556)]
theorem point_links_checked63034 : (cuts63034.take 1).map (fun c => (8265924609-1+2*2^10*c.k,114525256782126+c.lower,114525645538109+c.upper)) = pointBounds63034 := by
 decide +kernel
def cuts63035 : List PrefixCut := [⟨64,195081796,195081909⟩]
theorem checked63035 : checkPrefixCuts (2^48) 8266055681 10 Manual.Count131072.C063035.packed 64 cuts63035 = true := by
 decide +kernel
def cuts63036 : List PrefixCut := [⟨11,34119416,34119437⟩,
⟨64,198688108,198688223⟩]
theorem checked63036 : checkPrefixCuts (2^48) 8266186753 10 Manual.Count131072.C063036.packed 64 cuts63036 = true := by
 decide +kernel
def pointBounds63036 : List (Nat × Nat × Nat) := [(8266209280,114525683690222,114526072446451)]
theorem point_links_checked63036 : (cuts63036.take 1).map (fun c => (8266186753-1+2*2^10*c.k,114525649570806+c.lower,114526038327014+c.upper)) = pointBounds63036 := by
 decide +kernel
def cuts63037 : List PrefixCut := [⟨64,194428619,194428730⟩]
theorem checked63037 : checkPrefixCuts (2^48) 8266317825 10 Manual.Count131072.C063037.packed 64 cuts63037 = true := by
 decide +kernel
def cuts63038 : List PrefixCut := [⟨10,30713314,30713333⟩,
⟨64,195889707,195889821⟩]
theorem checked63038 : checkPrefixCuts (2^48) 8266448897 10 Manual.Count131072.C063038.packed 64 cuts63038 = true := by
 decide +kernel
def pointBounds63038 : List (Nat × Nat × Nat) := [(8266469376,114526073400847,114526462157300)]
theorem point_links_checked63038 : (cuts63038.take 1).map (fun c => (8266448897-1+2*2^10*c.k,114526042687533+c.lower,114526431443967+c.upper)) = pointBounds63038 := by
 decide +kernel
def cuts63039 : List PrefixCut := [⟨64,194592749,194592852⟩]
theorem checked63039 : checkPrefixCuts (2^48) 8266579969 10 Manual.Count131072.C063039.packed 64 cuts63039 = true := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000094
