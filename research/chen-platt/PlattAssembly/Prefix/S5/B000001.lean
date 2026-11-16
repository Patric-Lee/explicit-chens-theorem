import PlattAssemblyKernel
import PlattCertificates.Count131072.C040032
import PlattCertificates.Count131072.C040033
import PlattCertificates.Count131072.C040034
import PlattCertificates.Count131072.C040035
import PlattCertificates.Count131072.C040036
import PlattCertificates.Count131072.C040037
import PlattCertificates.Count131072.C040038
import PlattCertificates.Count131072.C040039
import PlattCertificates.Count131072.C040040
import PlattCertificates.Count131072.C040041
import PlattCertificates.Count131072.C040042
import PlattCertificates.Count131072.C040043
import PlattCertificates.Count131072.C040044
import PlattCertificates.Count131072.C040045
import PlattCertificates.Count131072.C040046
import PlattCertificates.Count131072.C040047
import PlattCertificates.Count131072.C040048
import PlattCertificates.Count131072.C040049
import PlattCertificates.Count131072.C040050
import PlattCertificates.Count131072.C040051
import PlattCertificates.Count131072.C040052
import PlattCertificates.Count131072.C040053
import PlattCertificates.Count131072.C040054
import PlattCertificates.Count131072.C040055
import PlattCertificates.Count131072.C040056
import PlattCertificates.Count131072.C040057
import PlattCertificates.Count131072.C040058
import PlattCertificates.Count131072.C040059
import PlattCertificates.Count131072.C040060
import PlattCertificates.Count131072.C040061
import PlattCertificates.Count131072.C040062
import PlattCertificates.Count131072.C040063
namespace ChenEffective.PlattWindow.Assembly.Prefix.S5.B000001
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts40032 : List PrefixCut := [⟨4,18975798,18975808⟩,
⟨64,310845630,310845816⟩]
theorem checked40032 : checkPrefixCuts (2^48) 5251006465 10 Manual.Count131072.C040032.packed 64 cuts40032 = true := by
 decide +kernel
def pointBounds40032 : List (Nat × Nat × Nat) := [(5251014656,108876306334891,108876691846466)]
theorem point_links_checked40032 : (cuts40032.take 1).map (fun c => (5251006465-1+2*2^10*c.k,108876287359093+c.lower,108876672870658+c.upper)) = pointBounds40032 := by
 decide +kernel
def cuts40033 : List PrefixCut := [⟨21,102112631,102112692⟩,
⟨64,315447660,315447847⟩]
theorem checked40033 : checkPrefixCuts (2^48) 5251137537 10 Manual.Count131072.C040033.packed 64 cuts40033 = true := by
 decide +kernel
def pointBounds40033 : List (Nat × Nat × Nat) := [(5251180544,108876700317354,108877085829166)]
theorem point_links_checked40033 : (cuts40033.take 1).map (fun c => (5251137537-1+2*2^10*c.k,108876598204723+c.lower,108876983716474+c.upper)) = pointBounds40033 := by
 decide +kernel
def cuts40034 : List PrefixCut := [⟨38,187656810,187656920⟩,
⟨64,317369409,317369597⟩]
theorem checked40034 : checkPrefixCuts (2^48) 5251268609 10 Manual.Count131072.C040034.packed 64 cuts40034 = true := by
 decide +kernel
def pointBounds40034 : List (Nat × Nat × Nat) := [(5251346432,108877101309193,108877486821241)]
theorem point_links_checked40034 : (cuts40034.take 1).map (fun c => (5251268609-1+2*2^10*c.k,108876913652383+c.lower,108877299164321+c.upper)) = pointBounds40034 := by
 decide +kernel
def cuts40035 : List PrefixCut := [⟨55,267621788,267621949⟩,
⟨64,310179182,310179369⟩]
theorem checked40035 : checkPrefixCuts (2^48) 5251399681 10 Manual.Count131072.C040035.packed 64 cuts40035 = true := by
 decide +kernel
def pointBounds40035 : List (Nat × Nat × Nat) := [(5251512320,108877498643580,108877884155867)]
theorem point_links_checked40035 : (cuts40035.take 1).map (fun c => (5251399681-1+2*2^10*c.k,108877231021792+c.lower,108877616533918+c.upper)) = pointBounds40035 := by
 decide +kernel
def cuts40036 : List PrefixCut := [⟨64,311511389,311511578⟩]
theorem checked40036 : checkPrefixCuts (2^48) 5251530753 10 Manual.Count131072.C040036.packed 64 cuts40036 = true := by
 decide +kernel
def cuts40037 : List PrefixCut := [⟨8,40037120,40037144⟩,
⟨64,313218727,313218916⟩]
theorem checked40037 : checkPrefixCuts (2^48) 5251661825 10 Manual.Count131072.C040037.packed 64 cuts40037 = true := by
 decide +kernel
def pointBounds40037 : List (Nat × Nat × Nat) := [(5251678208,108877892749483,108878278262009)]
theorem point_links_checked40037 : (cuts40037.take 1).map (fun c => (5251661825-1+2*2^10*c.k,108877852712363+c.lower,108878238224865+c.upper)) = pointBounds40037 := by
 decide +kernel
def cuts40038 : List PrefixCut := [⟨25,124234840,124234914⟩,
⟨64,315515523,315515713⟩]
theorem checked40038 : checkPrefixCuts (2^48) 5251792897 10 Manual.Count131072.C040038.packed 64 cuts40038 = true := by
 decide +kernel
def pointBounds40038 : List (Nat × Nat × Nat) := [(5251844096,108878290165930,108878675678695)]
theorem point_links_checked40038 : (cuts40038.take 1).map (fun c => (5251792897-1+2*2^10*c.k,108878165931090+c.lower,108878551443781+c.upper)) = pointBounds40038 := by
 decide +kernel
def cuts40039 : List PrefixCut := [⟨42,207570297,207570422⟩,
⟨64,314703741,314703930⟩]
theorem checked40039 : checkPrefixCuts (2^48) 5251923969 10 Manual.Count131072.C040039.packed 64 cuts40039 = true := by
 decide +kernel
def pointBounds40039 : List (Nat × Nat × Nat) := [(5252009984,108878689016910,108879074529916)]
theorem point_links_checked40039 : (cuts40039.take 1).map (fun c => (5251923969-1+2*2^10*c.k,108878481446613+c.lower,108878866959494+c.upper)) = pointBounds40039 := by
 decide +kernel
def cuts40040 : List PrefixCut := [⟨59,289186028,289186198⟩,
⟨64,315446108,315446293⟩]
theorem checked40040 : checkPrefixCuts (2^48) 5252055041 10 Manual.Count131072.C040040.packed 64 cuts40040 = true := by
 decide +kernel
def pointBounds40040 : List (Nat × Nat × Nat) := [(5252175872,108879085336382,108879470849622)]
theorem point_links_checked40040 : (cuts40040.take 1).map (fun c => (5252055041-1+2*2^10*c.k,108878796150354+c.lower,108879181663424+c.upper)) = pointBounds40040 := by
 decide +kernel
def cuts40041 : List PrefixCut := [⟨64,310883022,310883204⟩]
theorem checked40041 : checkPrefixCuts (2^48) 5252186113 10 Manual.Count131072.C040041.packed 64 cuts40041 = true := by
 decide +kernel
def cuts40042 : List PrefixCut := [⟨12,57931321,57931355⟩,
⟨64,316287812,316287996⟩]
theorem checked40042 : checkPrefixCuts (2^48) 5252317185 10 Manual.Count131072.C040042.packed 64 cuts40042 = true := by
 decide +kernel
def pointBounds40042 : List (Nat × Nat × Nat) := [(5252341760,108879480410805,108879865924276)]
theorem point_links_checked40042 : (cuts40042.take 1).map (fun c => (5252317185-1+2*2^10*c.k,108879422479484+c.lower,108879807992921+c.upper)) = pointBounds40042 := by
 decide +kernel
def cuts40043 : List PrefixCut := [⟨29,142653848,142653931⟩,
⟨64,317458893,317459078⟩]
theorem checked40043 : checkPrefixCuts (2^48) 5252448257 10 Manual.Count131072.C040043.packed 64 cuts40043 = true := by
 decide +kernel
def pointBounds40043 : List (Nat × Nat × Nat) := [(5252507648,108879881421144,108880266934848)]
theorem point_links_checked40043 : (cuts40043.take 1).map (fun c => (5252448257-1+2*2^10*c.k,108879738767296+c.lower,108880124280917+c.upper)) = pointBounds40043 := by
 decide +kernel
def cuts40044 : List PrefixCut := [⟨46,224156351,224156482⟩,
⟨64,310806182,310806367⟩]
theorem checked40044 : checkPrefixCuts (2^48) 5252579329 10 Manual.Count131072.C040044.packed 64 cuts40044 = true := by
 decide +kernel
def pointBounds40044 : List (Nat × Nat × Nat) := [(5252673536,108880280382540,108880665896477)]
theorem point_links_checked40044 : (cuts40044.take 1).map (fun c => (5252579329-1+2*2^10*c.k,108880056226189+c.lower,108880441739995+c.upper)) = pointBounds40044 := by
 decide +kernel
def cuts40045 : List PrefixCut := [⟨63,309512421,309512600⟩,
⟨64,313852828,313853010⟩]
theorem checked40045 : checkPrefixCuts (2^48) 5252710401 10 Manual.Count131072.C040045.packed 64 cuts40045 = true := by
 decide +kernel
def pointBounds40045 : List (Nat × Nat × Nat) := [(5252839424,108880676544792,108881062058962)]
theorem point_links_checked40045 : (cuts40045.take 1).map (fun c => (5252710401-1+2*2^10*c.k,108880367032371+c.lower,108880752546362+c.upper)) = pointBounds40045 := by
 decide +kernel
def cuts40046 : List PrefixCut := [⟨64,314916670,314916857⟩]
theorem checked40046 : checkPrefixCuts (2^48) 5252841473 10 Manual.Count131072.C040046.packed 64 cuts40046 = true := by
 decide +kernel
def cuts40047 : List PrefixCut := [⟨16,79303967,79304012⟩,
⟨64,315123141,315123326⟩]
theorem checked40047 : checkPrefixCuts (2^48) 5252972545 10 Manual.Count131072.C040047.packed 64 cuts40047 = true := by
 decide +kernel
def pointBounds40047 : List (Nat × Nat × Nat) := [(5253005312,108881075105836,108881460620241)]
theorem point_links_checked40047 : (cuts40047.take 1).map (fun c => (5252972545-1+2*2^10*c.k,108880995801869+c.lower,108881381316229+c.upper)) = pointBounds40047 := by
 decide +kernel
def cuts40048 : List PrefixCut := [⟨33,161014652,161014749⟩,
⟨64,311632479,311632664⟩]
theorem checked40048 : checkPrefixCuts (2^48) 5253103617 10 Manual.Count131072.C040048.packed 64 cuts40048 = true := by
 decide +kernel
def pointBounds40048 : List (Nat × Nat × Nat) := [(5253171200,108881471939662,108881857454304)]
theorem point_links_checked40048 : (cuts40048.take 1).map (fun c => (5253103617-1+2*2^10*c.k,108881310925010+c.lower,108881696439555+c.upper)) = pointBounds40048 := by
 decide +kernel
def cuts40049 : List PrefixCut := [⟨50,244060239,244060385⟩,
⟨64,312964198,312964384⟩]
theorem checked40049 : checkPrefixCuts (2^48) 5253234689 10 Manual.Count131072.C040049.packed 64 cuts40049 = true := by
 decide +kernel
def pointBounds40049 : List (Nat × Nat × Nat) := [(5253337088,108881866617728,108882252132604)]
theorem point_links_checked40049 : (cuts40049.take 1).map (fun c => (5253234689-1+2*2^10*c.k,108881622557489+c.lower,108882008072219+c.upper)) = pointBounds40049 := by
 decide +kernel
def cuts40050 : List PrefixCut := [⟨64,314456621,314456806⟩]
theorem checked40050 : checkPrefixCuts (2^48) 5253365761 10 Manual.Count131072.C040050.packed 64 cuts40050 = true := by
 decide +kernel
def cuts40051 : List PrefixCut := [⟨3,14305472,14305481⟩,
⟨64,311662705,311662886⟩]
theorem checked40051 : checkPrefixCuts (2^48) 5253496833 10 Manual.Count131072.C040051.packed 64 cuts40051 = true := by
 decide +kernel
def pointBounds40051 : List (Nat × Nat × Nat) := [(5253502976,108882264283780,108882649798890)]
theorem point_links_checked40051 : (cuts40051.take 1).map (fun c => (5253496833-1+2*2^10*c.k,108882249978308+c.lower,108882635493409+c.upper)) = pointBounds40051 := by
 decide +kernel
def cuts40052 : List PrefixCut := [⟨20,97617356,97617413⟩,
⟨64,314119434,314119619⟩]
theorem checked40052 : checkPrefixCuts (2^48) 5253627905 10 Manual.Count131072.C040052.packed 64 cuts40052 = true := by
 decide +kernel
def pointBounds40052 : List (Nat × Nat × Nat) := [(5253668864,108882659258369,108883044773708)]
theorem point_links_checked40052 : (cuts40052.take 1).map (fun c => (5253627905-1+2*2^10*c.k,108882561641013+c.lower,108882947156295+c.upper)) = pointBounds40052 := by
 decide +kernel
def cuts40053 : List PrefixCut := [⟨37,177174253,177174357⟩,
⟨64,310039879,310040064⟩]
theorem checked40053 : checkPrefixCuts (2^48) 5253758977 10 Manual.Count131072.C040053.packed 64 cuts40053 = true := by
 decide +kernel
def pointBounds40053 : List (Nat × Nat × Nat) := [(5253834752,108883052934700,108883438450271)]
theorem point_links_checked40053 : (cuts40053.take 1).map (fun c => (5253758977-1+2*2^10*c.k,108882875760447+c.lower,108883261275914+c.upper)) = pointBounds40053 := by
 decide +kernel
def cuts40054 : List PrefixCut := [⟨54,259566059,259566217⟩,
⟨64,308585662,308585849⟩]
theorem checked40054 : checkPrefixCuts (2^48) 5253890049 10 Manual.Count131072.C040054.packed 64 cuts40054 = true := by
 decide +kernel
def pointBounds40054 : List (Nat × Nat × Nat) := [(5254000640,108883445366385,108883830882195)]
theorem point_links_checked40054 : (cuts40054.take 1).map (fun c => (5253890049-1+2*2^10*c.k,108883185800326+c.lower,108883571315978+c.upper)) = pointBounds40054 := by
 decide +kernel
def cuts40055 : List PrefixCut := [⟨64,311738723,311738911⟩]
theorem checked40055 : checkPrefixCuts (2^48) 5254021121 10 Manual.Count131072.C040055.packed 64 cuts40055 = true := by
 decide +kernel
def cuts40056 : List PrefixCut := [⟨7,34285967,34285988⟩,
⟨64,311355993,311356179⟩]
theorem checked40056 : checkPrefixCuts (2^48) 5254152193 10 Manual.Count131072.C040056.packed 64 cuts40056 = true := by
 decide +kernel
def pointBounds40056 : List (Nat × Nat × Nat) := [(5254166528,108883840410678,108884225926726)]
theorem point_links_checked40056 : (cuts40056.take 1).map (fun c => (5254152193-1+2*2^10*c.k,108883806124711+c.lower,108884191640738+c.upper)) = pointBounds40056 := by
 decide +kernel
def cuts40057 : List PrefixCut := [⟨24,119140365,119140436⟩,
⟨64,316544488,316544675⟩]
theorem checked40057 : checkPrefixCuts (2^48) 5254283265 10 Manual.Count131072.C040057.packed 64 cuts40057 = true := by
 decide +kernel
def pointBounds40057 : List (Nat × Nat × Nat) := [(5254332416,108884236621069,108884622137353)]
theorem point_links_checked40057 : (cuts40057.take 1).map (fun c => (5254283265-1+2*2^10*c.k,108884117480704+c.lower,108884502996917+c.upper)) = pointBounds40057 := by
 decide +kernel
def cuts40058 : List PrefixCut := [⟨41,198097404,198097519⟩,
⟨64,310751173,310751354⟩]
theorem checked40058 : checkPrefixCuts (2^48) 5254414337 10 Manual.Count131072.C040058.packed 64 cuts40058 = true := by
 decide +kernel
def pointBounds40058 : List (Nat × Nat × Nat) := [(5254498304,108884632122596,108885017639111)]
theorem point_links_checked40058 : (cuts40058.take 1).map (fun c => (5254414337-1+2*2^10*c.k,108884434025192+c.lower,108884819541592+c.upper)) = pointBounds40058 := by
 decide +kernel
def cuts40059 : List PrefixCut := [⟨58,280371137,280371306⟩,
⟨64,310047041,310047228⟩]
theorem checked40059 : checkPrefixCuts (2^48) 5254545409 10 Manual.Count131072.C040059.packed 64 cuts40059 = true := by
 decide +kernel
def pointBounds40059 : List (Nat × Nat × Nat) := [(5254664192,108885025147502,108885410664252)]
theorem point_links_checked40059 : (cuts40059.take 1).map (fun c => (5254545409-1+2*2^10*c.k,108884744776365+c.lower,108885130292946+c.upper)) = pointBounds40059 := by
 decide +kernel
def cuts40060 : List PrefixCut := [⟨64,311860565,311860748⟩]
theorem checked40060 : checkPrefixCuts (2^48) 5254676481 10 Manual.Count131072.C040060.packed 64 cuts40060 = true := by
 decide +kernel
def cuts40061 : List PrefixCut := [⟨11,53565100,53565129⟩,
⟨64,315495173,315495360⟩]
theorem checked40061 : checkPrefixCuts (2^48) 5254807553 10 Manual.Count131072.C040061.packed 64 cuts40061 = true := by
 decide +kernel
def pointBounds40061 : List (Nat × Nat × Nat) := [(5254830080,108885420249071,108885805766051)]
theorem point_links_checked40061 : (cuts40061.take 1).map (fun c => (5254807553-1+2*2^10*c.k,108885366683971+c.lower,108885752200922+c.upper)) = pointBounds40061 := by
 decide +kernel
def cuts40062 : List PrefixCut := [⟨28,141032919,141033001⟩,
⟨64,314898136,314898323⟩]
theorem checked40062 : checkPrefixCuts (2^48) 5254938625 10 Manual.Count131072.C040062.packed 64 cuts40062 = true := by
 decide +kernel
def pointBounds40062 : List (Nat × Nat × Nat) := [(5254995968,108885823212063,108886208729283)]
theorem point_links_checked40062 : (cuts40062.take 1).map (fun c => (5254938625-1+2*2^10*c.k,108885682179144+c.lower,108886067696282+c.upper)) = pointBounds40062 := by
 decide +kernel
def cuts40063 : List PrefixCut := [⟨45,219550943,219551078⟩,
⟨64,313122716,313122905⟩]
theorem checked40063 : checkPrefixCuts (2^48) 5255069697 10 Manual.Count131072.C040063.packed 64 cuts40063 = true := by
 decide +kernel
def pointBounds40063 : List (Nat × Nat × Nat) := [(5255161856,108886216628223,108886602145683)]
theorem point_links_checked40063 : (cuts40063.take 1).map (fun c => (5255069697-1+2*2^10*c.k,108885997077280+c.lower,108886382594605+c.upper)) = pointBounds40063 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S5.B000001
