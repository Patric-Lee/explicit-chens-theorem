import PlattAssemblyKernel
import PlattCertificates.Count131072.C059920
import PlattCertificates.Count131072.C059921
import PlattCertificates.Count131072.C059922
import PlattCertificates.Count131072.C059923
import PlattCertificates.Count131072.C059924
import PlattCertificates.Count131072.C059925
import PlattCertificates.Count131072.C059926
import PlattCertificates.Count131072.C059927
import PlattCertificates.Count131072.C059928
import PlattCertificates.Count131072.C059929
import PlattCertificates.Count131072.C059930
import PlattCertificates.Count131072.C059931
import PlattCertificates.Count131072.C059932
import PlattCertificates.Count131072.C059933
import PlattCertificates.Count131072.C059934
import PlattCertificates.Count131072.C059935
import PlattCertificates.Count131072.C059936
import PlattCertificates.Count131072.C059937
import PlattCertificates.Count131072.C059938
import PlattCertificates.Count131072.C059939
import PlattCertificates.Count131072.C059940
import PlattCertificates.Count131072.C059941
import PlattCertificates.Count131072.C059942
import PlattCertificates.Count131072.C059943
import PlattCertificates.Count131072.C059944
import PlattCertificates.Count131072.C059945
import PlattCertificates.Count131072.C059946
import PlattCertificates.Count131072.C059947
import PlattCertificates.Count131072.C059948
import PlattCertificates.Count131072.C059949
import PlattCertificates.Count131072.C059950
import PlattCertificates.Count131072.C059951
namespace ChenEffective.PlattWindow.Assembly.Prefix.S6.B000310
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts59920 : List PrefixCut := [⟨64,203821124,203821244⟩]
theorem checked59920 : checkPrefixCuts (2^48) 7857766401 10 Manual.Count131072.C059920.packed 64 cuts59920 = true := by
 decide +kernel
def cuts59921 : List PrefixCut := [⟨55,177095963,177096066⟩,
⟨64,207184831,207184950⟩]
theorem checked59921 : checkPrefixCuts (2^48) 7857897473 10 Manual.Count131072.C059921.packed 64 cuts59921 = true := by
 decide +kernel
def pointBounds59921 : List (Nat × Nat × Nat) := [(7858010112,113900704196521,113901092594534)]
theorem point_links_checked59921 : (cuts59921.take 1).map (fun c => (7857897473-1+2*2^10*c.k,113900527100558+c.lower,113900915498468+c.upper)) = pointBounds59921 := by
 decide +kernel
def cuts59922 : List PrefixCut := [⟨64,204638180,204638296⟩]
theorem checked59922 : checkPrefixCuts (2^48) 7858028545 10 Manual.Count131072.C059922.packed 64 cuts59922 = true := by
 decide +kernel
def cuts59923 : List PrefixCut := [⟨47,151013854,151013942⟩,
⟨64,205745168,205745290⟩]
theorem checked59923 : checkPrefixCuts (2^48) 7858159617 10 Manual.Count131072.C059923.packed 64 cuts59923 = true := by
 decide +kernel
def pointBounds59923 : List (Nat × Nat × Nat) := [(7858255872,113901089937423,113901478335656)]
theorem point_links_checked59923 : (cuts59923.take 1).map (fun c => (7858159617-1+2*2^10*c.k,113900938923569+c.lower,113901327321714+c.upper)) = pointBounds59923 := by
 decide +kernel
def cuts59924 : List PrefixCut := [⟨64,204308992,204309111⟩]
theorem checked59924 : checkPrefixCuts (2^48) 7858290689 10 Manual.Count131072.C059924.packed 64 cuts59924 = true := by
 decide +kernel
def cuts59925 : List PrefixCut := [⟨39,126151230,126151301⟩,
⟨64,207242651,207242768⟩]
theorem checked59925 : checkPrefixCuts (2^48) 7858421761 10 Manual.Count131072.C059925.packed 64 cuts59925 = true := by
 decide +kernel
def pointBounds59925 : List (Nat × Nat × Nat) := [(7858501632,113901475128959,113901863527416)]
theorem point_links_checked59925 : (cuts59925.take 1).map (fun c => (7858421761-1+2*2^10*c.k,113901348977729+c.lower,113901737376115+c.upper)) = pointBounds59925 := by
 decide +kernel
def cuts59926 : List PrefixCut := [⟨64,202654573,202654691⟩]
theorem checked59926 : checkPrefixCuts (2^48) 7858552833 10 Manual.Count131072.C059926.packed 64 cuts59926 = true := by
 decide +kernel
def cuts59927 : List PrefixCut := [⟨31,101146944,101147002⟩,
⟨64,207128290,207128410⟩]
theorem checked59927 : checkPrefixCuts (2^48) 7858683905 10 Manual.Count131072.C059927.packed 64 cuts59927 = true := by
 decide +kernel
def pointBounds59927 : List (Nat × Nat × Nat) := [(7858747392,113901860021897,113902248420576)]
theorem point_links_checked59927 : (cuts59927.take 1).map (fun c => (7858683905-1+2*2^10*c.k,113901758874953+c.lower,113902147273574+c.upper)) = pointBounds59927 := by
 decide +kernel
def cuts59928 : List PrefixCut := [⟨64,206802494,206802613⟩]
theorem checked59928 : checkPrefixCuts (2^48) 7858814977 10 Manual.Count131072.C059928.packed 64 cuts59928 = true := by
 decide +kernel
def cuts59929 : List PrefixCut := [⟨23,72526890,72526933⟩,
⟨64,203718887,203719011⟩]
theorem checked59929 : checkPrefixCuts (2^48) 7858946049 10 Manual.Count131072.C059929.packed 64 cuts59929 = true := by
 decide +kernel
def pointBounds59929 : List (Nat × Nat × Nat) := [(7858993152,113902245332627,113902633731530)]
theorem point_links_checked59929 : (cuts59929.take 1).map (fun c => (7858946049-1+2*2^10*c.k,113902172805737+c.lower,113902561204597+c.upper)) = pointBounds59929 := by
 decide +kernel
def cuts59930 : List PrefixCut := [⟨64,204539251,204539365⟩]
theorem checked59930 : checkPrefixCuts (2^48) 7859077121 10 Manual.Count131072.C059930.packed 64 cuts59930 = true := by
 decide +kernel
def cuts59931 : List PrefixCut := [⟨15,47024562,47024591⟩,
⟨64,206899574,206899692⟩]
theorem checked59931 : checkPrefixCuts (2^48) 7859208193 10 Manual.Count131072.C059931.packed 64 cuts59931 = true := by
 decide +kernel
def pointBounds59931 : List (Nat × Nat × Nat) := [(7859238912,113902628088437,113903016487564)]
theorem point_links_checked59931 : (cuts59931.take 1).map (fun c => (7859208193-1+2*2^10*c.k,113902581063875+c.lower,113902969462973+c.upper)) = pointBounds59931 := by
 decide +kernel
def cuts59932 : List PrefixCut := [⟨64,206752872,206752988⟩]
theorem checked59932 : checkPrefixCuts (2^48) 7859339265 10 Manual.Count131072.C059932.packed 64 cuts59932 = true := by
 decide +kernel
def cuts59933 : List PrefixCut := [⟨7,21416435,21416449⟩,
⟨64,205424334,205424456⟩]
theorem checked59933 : checkPrefixCuts (2^48) 7859470337 10 Manual.Count131072.C059933.packed 64 cuts59933 = true := by
 decide +kernel
def pointBounds59933 : List (Nat × Nat × Nat) := [(7859484672,113903016132756,113903404532102)]
theorem point_links_checked59933 : (cuts59933.take 1).map (fun c => (7859470337-1+2*2^10*c.k,113902994716321+c.lower,113903383115653+c.upper)) = pointBounds59933 := by
 decide +kernel
def cuts59934 : List PrefixCut := [⟨63,202627566,202627685⟩,
⟨64,205635797,205635918⟩]
theorem checked59934 : checkPrefixCuts (2^48) 7859601409 10 Manual.Count131072.C059934.packed 64 cuts59934 = true := by
 decide +kernel
def pointBounds59934 : List (Nat × Nat × Nat) := [(7859730432,113903402768221,113903791167794)]
theorem point_links_checked59934 : (cuts59934.take 1).map (fun c => (7859601409-1+2*2^10*c.k,113903200140655+c.lower,113903588540109+c.upper)) = pointBounds59934 := by
 decide +kernel
def cuts59935 : List PrefixCut := [⟨64,206635104,206635221⟩]
theorem checked59935 : checkPrefixCuts (2^48) 7859732481 10 Manual.Count131072.C059935.packed 64 cuts59935 = true := by
 decide +kernel
def cuts59936 : List PrefixCut := [⟨55,179988210,179988312⟩,
⟨64,207992509,207992625⟩]
theorem checked59936 : checkPrefixCuts (2^48) 7859863553 10 Manual.Count131072.C059936.packed 64 cuts59936 = true := by
 decide +kernel
def pointBounds59936 : List (Nat × Nat × Nat) := [(7859976192,113903792399766,113904180799560)]
theorem point_links_checked59936 : (cuts59936.take 1).map (fun c => (7859863553-1+2*2^10*c.k,113903612411556+c.lower,113904000811248+c.upper)) = pointBounds59936 := by
 decide +kernel
def cuts59937 : List PrefixCut := [⟨64,205016726,205016843⟩]
theorem checked59937 : checkPrefixCuts (2^48) 7859994625 10 Manual.Count131072.C059937.packed 64 cuts59937 = true := by
 decide +kernel
def cuts59938 : List PrefixCut := [⟨47,152659155,152659241⟩,
⟨64,207734881,207735000⟩]
theorem checked59938 : checkPrefixCuts (2^48) 7860125697 10 Manual.Count131072.C059938.packed 64 cuts59938 = true := by
 decide +kernel
def pointBounds59938 : List (Nat × Nat × Nat) := [(7860221952,113904178079946,113904566479957)]
theorem point_links_checked59938 : (cuts59938.take 1).map (fun c => (7860125697-1+2*2^10*c.k,113904025420791+c.lower,113904413820716+c.upper)) = pointBounds59938 := by
 decide +kernel
def cuts59939 : List PrefixCut := [⟨64,205582840,205582951⟩]
theorem checked59939 : checkPrefixCuts (2^48) 7860256769 10 Manual.Count131072.C059939.packed 64 cuts59939 = true := by
 decide +kernel
def cuts59940 : List PrefixCut := [⟨39,127158144,127158218⟩,
⟨64,207298255,207298372⟩]
theorem checked59940 : checkPrefixCuts (2^48) 7860387841 10 Manual.Count131072.C059940.packed 64 cuts59940 = true := by
 decide +kernel
def pointBounds59940 : List (Nat × Nat × Nat) := [(7860467712,113904565896656,113904954296885)]
theorem point_links_checked59940 : (cuts59940.take 1).map (fun c => (7860387841-1+2*2^10*c.k,113904438738512+c.lower,113904827138667+c.upper)) = pointBounds59940 := by
 decide +kernel
def cuts59941 : List PrefixCut := [⟨64,203391661,203391781⟩]
theorem checked59941 : checkPrefixCuts (2^48) 7860518913 10 Manual.Count131072.C059941.packed 64 cuts59941 = true := by
 decide +kernel
def cuts59942 : List PrefixCut := [⟨31,97218580,97218636⟩,
⟨64,203531502,203531616⟩]
theorem checked59942 : checkPrefixCuts (2^48) 7860649985 10 Manual.Count131072.C059942.packed 64 cuts59942 = true := by
 decide +kernel
def pointBounds59942 : List (Nat × Nat × Nat) := [(7860713472,113904946647008,113905335047456)]
theorem point_links_checked59942 : (cuts59942.take 1).map (fun c => (7860649985-1+2*2^10*c.k,113904849428428+c.lower,113905237828820+c.upper)) = pointBounds59942 := by
 decide +kernel
def cuts59943 : List PrefixCut := [⟨64,207824997,207825111⟩]
theorem checked59943 : checkPrefixCuts (2^48) 7860781057 10 Manual.Count131072.C059943.packed 64 cuts59943 = true := by
 decide +kernel
def cuts59944 : List PrefixCut := [⟨23,74692970,74693013⟩,
⟨64,207248608,207248728⟩]
theorem checked59944 : checkPrefixCuts (2^48) 7860912129 10 Manual.Count131072.C059944.packed 64 cuts59944 = true := by
 decide +kernel
def pointBounds59944 : List (Nat × Nat × Nat) := [(7860959232,113905335477897,113905723878560)]
theorem point_links_checked59944 : (cuts59944.take 1).map (fun c => (7860912129-1+2*2^10*c.k,113905260784927+c.lower,113905649185547+c.upper)) = pointBounds59944 := by
 decide +kernel
def cuts59945 : List PrefixCut := [⟨64,204452291,204452406⟩]
theorem checked59945 : checkPrefixCuts (2^48) 7861043201 10 Manual.Count131072.C059945.packed 64 cuts59945 = true := by
 decide +kernel
def cuts59946 : List PrefixCut := [⟨15,47263439,47263469⟩,
⟨64,206776220,206776338⟩]
theorem checked59946 : checkPrefixCuts (2^48) 7861174273 10 Manual.Count131072.C059946.packed 64 cuts59946 = true := by
 decide +kernel
def pointBounds59946 : List (Nat × Nat × Nat) := [(7861204992,113905719749265,113906108150150)]
theorem point_links_checked59946 : (cuts59946.take 1).map (fun c => (7861174273-1+2*2^10*c.k,113905672485826+c.lower,113906060886681+c.upper)) = pointBounds59946 := by
 decide +kernel
def cuts59947 : List PrefixCut := [⟨64,207846932,207847053⟩]
theorem checked59947 : checkPrefixCuts (2^48) 7861305345 10 Manual.Count131072.C059947.packed 64 cuts59947 = true := by
 decide +kernel
def cuts59948 : List PrefixCut := [⟨7,21804927,21804940⟩,
⟨64,202723472,202723587⟩]
theorem checked59948 : checkPrefixCuts (2^48) 7861436417 10 Manual.Count131072.C059948.packed 64 cuts59948 = true := by
 decide +kernel
def pointBounds59948 : List (Nat × Nat × Nat) := [(7861450752,113906108913905,113906497315012)]
theorem point_links_checked59948 : (cuts59948.take 1).map (fun c => (7861436417-1+2*2^10*c.k,113906087108978+c.lower,113906475510072+c.upper)) = pointBounds59948 := by
 decide +kernel
def cuts59949 : List PrefixCut := [⟨63,206479482,206479597⟩,
⟨64,209665978,209666095⟩]
theorem checked59949 : checkPrefixCuts (2^48) 7861567489 10 Manual.Count131072.C059949.packed 64 cuts59949 = true := by
 decide +kernel
def pointBounds59949 : List (Nat × Nat × Nat) := [(7861696512,113906496311932,113906884713256)]
theorem point_links_checked59949 : (cuts59949.take 1).map (fun c => (7861567489-1+2*2^10*c.k,113906289832450+c.lower,113906678233659+c.upper)) = pointBounds59949 := by
 decide +kernel
def cuts59950 : List PrefixCut := [⟨64,204864871,204864986⟩]
theorem checked59950 : checkPrefixCuts (2^48) 7861698561 10 Manual.Count131072.C059950.packed 64 cuts59950 = true := by
 decide +kernel
def cuts59951 : List PrefixCut := [⟨55,176971600,176971697⟩,
⟨64,206472586,206472700⟩]
theorem checked59951 : checkPrefixCuts (2^48) 7861829633 10 Manual.Count131072.C059951.packed 64 cuts59951 = true := by
 decide +kernel
def pointBounds59951 : List (Nat × Nat × Nat) := [(7861942272,113906881334899,113907269736437)]
theorem point_links_checked59951 : (cuts59951.take 1).map (fun c => (7861829633-1+2*2^10*c.k,113906704363299+c.lower,113907092764740+c.upper)) = pointBounds59951 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S6.B000310
