import PlattAssemblyKernel
import PlattCertificates.Count131072.C070928
import PlattCertificates.Count131072.C070929
import PlattCertificates.Count131072.C070930
import PlattCertificates.Count131072.C070931
import PlattCertificates.Count131072.C070932
import PlattCertificates.Count131072.C070933
import PlattCertificates.Count131072.C070934
import PlattCertificates.Count131072.C070935
import PlattCertificates.Count131072.C070936
import PlattCertificates.Count131072.C070937
import PlattCertificates.Count131072.C070938
import PlattCertificates.Count131072.C070939
import PlattCertificates.Count131072.C070940
import PlattCertificates.Count131072.C070941
import PlattCertificates.Count131072.C070942
import PlattCertificates.Count131072.C070943
import PlattCertificates.Count131072.C070944
import PlattCertificates.Count131072.C070945
import PlattCertificates.Count131072.C070946
import PlattCertificates.Count131072.C070947
import PlattCertificates.Count131072.C070948
import PlattCertificates.Count131072.C070949
import PlattCertificates.Count131072.C070950
import PlattCertificates.Count131072.C070951
import PlattCertificates.Count131072.C070952
import PlattCertificates.Count131072.C070953
import PlattCertificates.Count131072.C070954
import PlattCertificates.Count131072.C070955
import PlattCertificates.Count131072.C070956
import PlattCertificates.Count131072.C070957
import PlattCertificates.Count131072.C070958
import PlattCertificates.Count131072.C070959
namespace ChenEffective.PlattWindow.Assembly.Prefix.S8.B000029
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts70928 : List PrefixCut := [⟨5,13195160,13195166⟩,
⟨64,174017602,174017705⟩]
theorem checked70928 : checkPrefixCuts (2^48) 9300606977 10 Manual.Count131072.C070928.packed 64 cuts70928 = true := by
 decide +kernel
def pointBounds70928 : List (Nat × Nat × Nat) := [(9300617216,115975265231928,115975654832281)]
theorem point_links_checked70928 : (cuts70928.take 1).map (fun c => (9300606977-1+2*2^10*c.k,115975252036768+c.lower,115975641637115+c.upper)) = pointBounds70928 := by
 decide +kernel
def cuts70929 : List PrefixCut := [⟨64,174408572,174408669⟩]
theorem checked70929 : checkPrefixCuts (2^48) 9300738049 10 Manual.Count131072.C070929.packed 64 cuts70929 = true := by
 decide +kernel
def cuts70930 : List PrefixCut := [⟨19,51326427,51326462⟩,
⟨64,172771901,172772006⟩]
theorem checked70930 : checkPrefixCuts (2^48) 9300869121 10 Manual.Count131072.C070930.packed 64 cuts70930 = true := by
 decide +kernel
def pointBounds70930 : List (Nat × Nat × Nat) := [(9300908032,115975651789369,115976041389951)]
theorem point_links_checked70930 : (cuts70930.take 1).map (fun c => (9300869121-1+2*2^10*c.k,115975600462942+c.lower,115975990063489+c.upper)) = pointBounds70930 := by
 decide +kernel
def cuts70931 : List PrefixCut := [⟨64,174040502,174040599⟩]
theorem checked70931 : checkPrefixCuts (2^48) 9301000193 10 Manual.Count131072.C070931.packed 64 cuts70931 = true := by
 decide +kernel
def cuts70932 : List PrefixCut := [⟨33,88880452,88880502⟩,
⟨64,172403883,172403987⟩]
theorem checked70932 : checkPrefixCuts (2^48) 9301131265 10 Manual.Count131072.C070932.packed 64 cuts70932 = true := by
 decide +kernel
def pointBounds70932 : List (Nat × Nat × Nat) := [(9301198848,115976036155797,115976425756596)]
theorem point_links_checked70932 : (cuts70932.take 1).map (fun c => (9301131265-1+2*2^10*c.k,115975947275345+c.lower,115976336876094+c.upper)) = pointBounds70932 := by
 decide +kernel
def cuts70933 : List PrefixCut := [⟨64,169254225,169254325⟩]
theorem checked70933 : checkPrefixCuts (2^48) 9301262337 10 Manual.Count131072.C070933.packed 64 cuts70933 = true := by
 decide +kernel
def cuts70934 : List PrefixCut := [⟨47,127824266,127824343⟩,
⟨64,173216086,173216190⟩]
theorem checked70934 : checkPrefixCuts (2^48) 9301393409 10 Manual.Count131072.C070934.packed 64 cuts70934 = true := by
 decide +kernel
def pointBounds70934 : List (Nat × Nat × Nat) := [(9301489664,115976416757719,115976806358749)]
theorem point_links_checked70934 : (cuts70934.take 1).map (fun c => (9301393409-1+2*2^10*c.k,115976288933453+c.lower,115976678534406+c.upper)) = pointBounds70934 := by
 decide +kernel
def cuts70935 : List PrefixCut := [⟨64,172396594,172396702⟩]
theorem checked70935 : checkPrefixCuts (2^48) 9301524481 10 Manual.Count131072.C070935.packed 64 cuts70935 = true := by
 decide +kernel
def cuts70936 : List PrefixCut := [⟨61,165222466,165222558⟩,
⟨64,173150668,173150765⟩]
theorem checked70936 : checkPrefixCuts (2^48) 9301655553 10 Manual.Count131072.C070936.packed 64 cuts70936 = true := by
 decide +kernel
def pointBounds70936 : List (Nat × Nat × Nat) := [(9301780480,115976799768599,115977189369856)]
theorem point_links_checked70936 : (cuts70936.take 1).map (fun c => (9301655553-1+2*2^10*c.k,115976634546133+c.lower,115977024147298+c.upper)) = pointBounds70936 := by
 decide +kernel
def cuts70937 : List PrefixCut := [⟨64,172936419,172936515⟩]
theorem checked70937 : checkPrefixCuts (2^48) 9301786625 10 Manual.Count131072.C070937.packed 64 cuts70937 = true := by
 decide +kernel
def cuts70938 : List PrefixCut := [⟨64,171663075,171663179⟩]
theorem checked70938 : checkPrefixCuts (2^48) 9301917697 10 Manual.Count131072.C070938.packed 64 cuts70938 = true := by
 decide +kernel
def cuts70939 : List PrefixCut := [⟨11,30077861,30077874⟩,
⟨64,173324921,173325027⟩]
theorem checked70939 : checkPrefixCuts (2^48) 9302048769 10 Manual.Count131072.C070939.packed 64 cuts70939 = true := by
 decide +kernel
def pointBounds70939 : List (Nat × Nat × Nat) := [(9302071296,115977182374156,115977571975631)]
theorem point_links_checked70939 : (cuts70939.take 1).map (fun c => (9302048769-1+2*2^10*c.k,115977152296295+c.lower,115977541897757+c.upper)) = pointBounds70939 := by
 decide +kernel
def cuts70940 : List PrefixCut := [⟨64,175198526,175198629⟩]
theorem checked70940 : checkPrefixCuts (2^48) 9302179841 10 Manual.Count131072.C070940.packed 64 cuts70940 = true := by
 decide +kernel
def cuts70941 : List PrefixCut := [⟨25,65963562,65963602⟩,
⟨64,171292707,171292810⟩]
theorem checked70941 : checkPrefixCuts (2^48) 9302310913 10 Manual.Count131072.C070941.packed 64 cuts70941 = true := by
 decide +kernel
def pointBounds70941 : List (Nat × Nat × Nat) := [(9302362112,115977566783304,115977956385015)]
theorem point_links_checked70941 : (cuts70941.take 1).map (fun c => (9302310913-1+2*2^10*c.k,115977500819742+c.lower,115977890421413+c.upper)) = pointBounds70941 := by
 decide +kernel
def cuts70942 : List PrefixCut := [⟨64,172379594,172379701⟩]
theorem checked70942 : checkPrefixCuts (2^48) 9302441985 10 Manual.Count131072.C070942.packed 64 cuts70942 = true := by
 decide +kernel
def cuts70943 : List PrefixCut := [⟨39,105780630,105780691⟩,
⟨64,173133605,173133709⟩]
theorem checked70943 : checkPrefixCuts (2^48) 9302573057 10 Manual.Count131072.C070943.packed 64 cuts70943 = true := by
 decide +kernel
def pointBounds70943 : List (Nat × Nat × Nat) := [(9302652928,115977950272673,115978339874615)]
theorem point_links_checked70943 : (cuts70943.take 1).map (fun c => (9302573057-1+2*2^10*c.k,115977844492043+c.lower,115978234093924+c.upper)) = pointBounds70943 := by
 decide +kernel
def cuts70944 : List PrefixCut := [⟨64,170680337,170680441⟩]
theorem checked70944 : checkPrefixCuts (2^48) 9302704129 10 Manual.Count131072.C070944.packed 64 cuts70944 = true := by
 decide +kernel
def cuts70945 : List PrefixCut := [⟨53,145534806,145534895⟩,
⟨64,175307205,175307313⟩]
theorem checked70945 : checkPrefixCuts (2^48) 9302835201 10 Manual.Count131072.C070945.packed 64 cuts70945 = true := by
 decide +kernel
def pointBounds70945 : List (Nat × Nat × Nat) := [(9302943744,115978333840791,115978723442969)]
theorem point_links_checked70945 : (cuts70945.take 1).map (fun c => (9302835201-1+2*2^10*c.k,115978188305985+c.lower,115978577908074+c.upper)) = pointBounds70945 := by
 decide +kernel
def cuts70946 : List PrefixCut := [⟨64,170494013,170494110⟩]
theorem checked70946 : checkPrefixCuts (2^48) 9302966273 10 Manual.Count131072.C070946.packed 64 cuts70946 = true := by
 decide +kernel
def cuts70947 : List PrefixCut := [⟨64,173154100,173154200⟩]
theorem checked70947 : checkPrefixCuts (2^48) 9303097345 10 Manual.Count131072.C070947.packed 64 cuts70947 = true := by
 decide +kernel
def cuts70948 : List PrefixCut := [⟨3,8199269,8199273⟩,
⟨64,172274252,172274353⟩]
theorem checked70948 : checkPrefixCuts (2^48) 9303228417 10 Manual.Count131072.C070948.packed 64 cuts70948 = true := by
 decide +kernel
def pointBounds70948 : List (Nat × Nat × Nat) := [(9303234560,115978715460572,115979105062970)]
theorem point_links_checked70948 : (cuts70948.take 1).map (fun c => (9303228417-1+2*2^10*c.k,115978707261303+c.lower,115979096863697+c.upper)) = pointBounds70948 := by
 decide +kernel
def cuts70949 : List PrefixCut := [⟨64,173330753,173330855⟩]
theorem checked70949 : checkPrefixCuts (2^48) 9303359489 10 Manual.Count131072.C070949.packed 64 cuts70949 = true := by
 decide +kernel
def cuts70950 : List PrefixCut := [⟨17,45503075,45503102⟩,
⟨64,171876081,171876184⟩]
theorem checked70950 : checkPrefixCuts (2^48) 9303490561 10 Manual.Count131072.C070950.packed 64 cuts70950 = true := by
 decide +kernel
def pointBounds70950 : List (Nat × Nat × Nat) := [(9303525376,115979098369383,115979487972007)]
theorem point_links_checked70950 : (cuts70950.take 1).map (fun c => (9303490561-1+2*2^10*c.k,115979052866308+c.lower,115979442468905+c.upper)) = pointBounds70950 := by
 decide +kernel
def cuts70951 : List PrefixCut := [⟨64,171934176,171934283⟩]
theorem checked70951 : checkPrefixCuts (2^48) 9303621633 10 Manual.Count131072.C070951.packed 64 cuts70951 = true := by
 decide +kernel
def cuts70952 : List PrefixCut := [⟨31,83258476,83258527⟩,
⟨64,172355309,172355415⟩]
theorem checked70952 : checkPrefixCuts (2^48) 9303752705 10 Manual.Count131072.C070952.packed 64 cuts70952 = true := by
 decide +kernel
def pointBounds70952 : List (Nat × Nat × Nat) := [(9303816192,115979479935041,115979869537899)]
theorem point_links_checked70952 : (cuts70952.take 1).map (fun c => (9303752705-1+2*2^10*c.k,115979396676565+c.lower,115979786279372+c.upper)) = pointBounds70952 := by
 decide +kernel
def cuts70953 : List PrefixCut := [⟨64,172231874,172231979⟩]
theorem checked70953 : checkPrefixCuts (2^48) 9303883777 10 Manual.Count131072.C070953.packed 64 cuts70953 = true := by
 decide +kernel
def cuts70954 : List PrefixCut := [⟨45,121283901,121283973⟩,
⟨64,173621062,173621166⟩]
theorem checked70954 : checkPrefixCuts (2^48) 9304014849 10 Manual.Count131072.C070954.packed 64 cuts70954 = true := by
 decide +kernel
def pointBounds70954 : List (Nat × Nat × Nat) := [(9304107008,115979862547649,115980252150739)]
theorem point_links_checked70954 : (cuts70954.take 1).map (fun c => (9304014849-1+2*2^10*c.k,115979741263748+c.lower,115980130866766+c.upper)) = pointBounds70954 := by
 decide +kernel
def cuts70955 : List PrefixCut := [⟨64,175645539,175645643⟩]
theorem checked70955 : checkPrefixCuts (2^48) 9304145921 10 Manual.Count131072.C070955.packed 64 cuts70955 = true := by
 decide +kernel
def cuts70956 : List PrefixCut := [⟨59,159367571,159367668⟩,
⟨64,173041383,173041487⟩]
theorem checked70956 : checkPrefixCuts (2^48) 9304276993 10 Manual.Count131072.C070956.packed 64 cuts70956 = true := by
 decide +kernel
def pointBounds70956 : List (Nat × Nat × Nat) := [(9304397824,115980249897920,115980639501243)]
theorem point_links_checked70956 : (cuts70956.take 1).map (fun c => (9304276993-1+2*2^10*c.k,115980090530349+c.lower,115980480133575+c.upper)) = pointBounds70956 := by
 decide +kernel
def cuts70957 : List PrefixCut := [⟨64,172524680,172524783⟩]
theorem checked70957 : checkPrefixCuts (2^48) 9304408065 10 Manual.Count131072.C070957.packed 64 cuts70957 = true := by
 decide +kernel
def cuts70958 : List PrefixCut := [⟨64,170525677,170525778⟩]
theorem checked70958 : checkPrefixCuts (2^48) 9304539137 10 Manual.Count131072.C070958.packed 64 cuts70958 = true := by
 decide +kernel
def cuts70959 : List PrefixCut := [⟨9,24745233,24745249⟩,
⟨64,171884560,171884659⟩]
theorem checked70959 : checkPrefixCuts (2^48) 9304670209 10 Manual.Count131072.C070959.packed 64 cuts70959 = true := by
 decide +kernel
def pointBounds70959 : List (Nat × Nat × Nat) := [(9304688640,115980631367322,115981020970872)]
theorem point_links_checked70959 : (cuts70959.take 1).map (fun c => (9304670209-1+2*2^10*c.k,115980606622089+c.lower,115980996225623+c.upper)) = pointBounds70959 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S8.B000029
