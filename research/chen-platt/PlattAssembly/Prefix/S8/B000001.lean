import PlattAssemblyKernel
import PlattCertificates.Count131072.C070032
import PlattCertificates.Count131072.C070033
import PlattCertificates.Count131072.C070034
import PlattCertificates.Count131072.C070035
import PlattCertificates.Count131072.C070036
import PlattCertificates.Count131072.C070037
import PlattCertificates.Count131072.C070038
import PlattCertificates.Count131072.C070039
import PlattCertificates.Count131072.C070040
import PlattCertificates.Count131072.C070041
import PlattCertificates.Count131072.C070042
import PlattCertificates.Count131072.C070043
import PlattCertificates.Count131072.C070044
import PlattCertificates.Count131072.C070045
import PlattCertificates.Count131072.C070046
import PlattCertificates.Count131072.C070047
import PlattCertificates.Count131072.C070048
import PlattCertificates.Count131072.C070049
import PlattCertificates.Count131072.C070050
import PlattCertificates.Count131072.C070051
import PlattCertificates.Count131072.C070052
import PlattCertificates.Count131072.C070053
import PlattCertificates.Count131072.C070054
import PlattCertificates.Count131072.C070055
import PlattCertificates.Count131072.C070056
import PlattCertificates.Count131072.C070057
import PlattCertificates.Count131072.C070058
import PlattCertificates.Count131072.C070059
import PlattCertificates.Count131072.C070060
import PlattCertificates.Count131072.C070061
import PlattCertificates.Count131072.C070062
import PlattCertificates.Count131072.C070063
namespace ChenEffective.PlattWindow.Assembly.Prefix.S8.B000001
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts70032 : List PrefixCut := [⟨38,104029667,104029727⟩,
⟨64,175078298,175078399⟩]
theorem checked70032 : checkPrefixCuts (2^48) 9183166465 10 Manual.Count131072.C070032.packed 64 cuts70032 = true := by
 decide +kernel
def pointBounds70032 : List (Nat × Nat × Nat) := [(9183244288,115819438271756,115819827780325)]
theorem point_links_checked70032 : (cuts70032.take 1).map (fun c => (9183166465-1+2*2^10*c.k,115819334242089+c.lower,115819723750598+c.upper)) = pointBounds70032 := by
 decide +kernel
def cuts70033 : List PrefixCut := [⟨64,174769294,174769407⟩]
theorem checked70033 : checkPrefixCuts (2^48) 9183297537 10 Manual.Count131072.C070033.packed 64 cuts70033 = true := by
 decide +kernel
def cuts70034 : List PrefixCut := [⟨51,141419712,141419793⟩,
⟨64,177801159,177801260⟩]
theorem checked70034 : checkPrefixCuts (2^48) 9183428609 10 Manual.Count131072.C070034.packed 64 cuts70034 = true := by
 decide +kernel
def pointBounds70034 : List (Nat × Nat × Nat) := [(9183533056,115819825509393,115820215018197)]
theorem point_links_checked70034 : (cuts70034.take 1).map (fun c => (9183428609-1+2*2^10*c.k,115819684089681+c.lower,115820073598404+c.upper)) = pointBounds70034 := by
 decide +kernel
def cuts70035 : List PrefixCut := [⟨64,174488458,174488557⟩]
theorem checked70035 : checkPrefixCuts (2^48) 9183559681 10 Manual.Count131072.C070035.packed 64 cuts70035 = true := by
 decide +kernel
def cuts70036 : List PrefixCut := [⟨64,173689086,173689192⟩]
theorem checked70036 : checkPrefixCuts (2^48) 9183690753 10 Manual.Count131072.C070036.packed 64 cuts70036 = true := by
 decide +kernel
def pointBounds70036 : List (Nat × Nat × Nat) := [(9183821824,115820210068384,115820599577413)]
theorem point_links_checked70036 : (cuts70036.take 1).map (fun c => (9183690753-1+2*2^10*c.k,115820036379298+c.lower,115820425888221+c.upper)) = pointBounds70036 := by
 decide +kernel
def cuts70037 : List PrefixCut := [⟨64,173778557,173778661⟩]
theorem checked70037 : checkPrefixCuts (2^48) 9183821825 10 Manual.Count131072.C070037.packed 64 cuts70037 = true := by
 decide +kernel
def cuts70038 : List PrefixCut := [⟨64,174266449,174266547⟩]
theorem checked70038 : checkPrefixCuts (2^48) 9183952897 10 Manual.Count131072.C070038.packed 64 cuts70038 = true := by
 decide +kernel
def cuts70039 : List PrefixCut := [⟨13,34448435,34448456⟩,
⟨64,173712286,173712391⟩]
theorem checked70039 : checkPrefixCuts (2^48) 9184083969 10 Manual.Count131072.C070039.packed 64 cuts70039 = true := by
 decide +kernel
def pointBounds70039 : List (Nat × Nat × Nat) := [(9184110592,115820592561825,115820982071077)]
theorem point_links_checked70039 : (cuts70039.take 1).map (fun c => (9184083969-1+2*2^10*c.k,115820558113390+c.lower,115820947622621+c.upper)) = pointBounds70039 := by
 decide +kernel
def cuts70040 : List PrefixCut := [⟨64,170154704,170154810⟩]
theorem checked70040 : checkPrefixCuts (2^48) 9184215041 10 Manual.Count131072.C070040.packed 64 cuts70040 = true := by
 decide +kernel
def cuts70041 : List PrefixCut := [⟨26,73032173,73032212⟩,
⟨64,176833344,176833445⟩]
theorem checked70041 : checkPrefixCuts (2^48) 9184346113 10 Manual.Count131072.C070041.packed 64 cuts70041 = true := by
 decide +kernel
def pointBounds70041 : List (Nat × Nat × Nat) := [(9184399360,115820975012553,115821364522034)]
theorem point_links_checked70041 : (cuts70041.take 1).map (fun c => (9184346113-1+2*2^10*c.k,115820901980380+c.lower,115821291489822+c.upper)) = pointBounds70041 := by
 decide +kernel
def cuts70042 : List PrefixCut := [⟨64,171835410,171835515⟩]
theorem checked70042 : checkPrefixCuts (2^48) 9184477185 10 Manual.Count131072.C070042.packed 64 cuts70042 = true := by
 decide +kernel
def cuts70043 : List PrefixCut := [⟨39,106005328,106005390⟩,
⟨64,175081451,175081554⟩]
theorem checked70043 : checkPrefixCuts (2^48) 9184608257 10 Manual.Count131072.C070043.packed 64 cuts70043 = true := by
 decide +kernel
def pointBounds70043 : List (Nat × Nat × Nat) := [(9184688128,115821356654462,115821746164172)]
theorem point_links_checked70043 : (cuts70043.take 1).map (fun c => (9184608257-1+2*2^10*c.k,115821250649134+c.lower,115821640158782+c.upper)) = pointBounds70043 := by
 decide +kernel
def cuts70044 : List PrefixCut := [⟨64,176580599,176580695⟩]
theorem checked70044 : checkPrefixCuts (2^48) 9184739329 10 Manual.Count131072.C070044.packed 64 cuts70044 = true := by
 decide +kernel
def cuts70045 : List PrefixCut := [⟨52,139466832,139466913⟩,
⟨64,172257088,172257187⟩]
theorem checked70045 : checkPrefixCuts (2^48) 9184870401 10 Manual.Count131072.C070045.packed 64 cuts70045 = true := by
 decide +kernel
def pointBounds70045 : List (Nat × Nat × Nat) := [(9184976896,115821741778016,115822131287944)]
theorem point_links_checked70045 : (cuts70045.take 1).map (fun c => (9184870401-1+2*2^10*c.k,115821602311184+c.lower,115821991821031+c.upper)) = pointBounds70045 := by
 decide +kernel
def cuts70046 : List PrefixCut := [⟨64,174920744,174920844⟩]
theorem checked70046 : checkPrefixCuts (2^48) 9185001473 10 Manual.Count131072.C070046.packed 64 cuts70046 = true := by
 decide +kernel
def cuts70047 : List PrefixCut := [⟨64,175316617,175316720⟩]
theorem checked70047 : checkPrefixCuts (2^48) 9185132545 10 Manual.Count131072.C070047.packed 64 cuts70047 = true := by
 decide +kernel
def cuts70048 : List PrefixCut := [⟨1,2604755,2604757⟩,
⟨64,175130237,175130343⟩]
theorem checked70048 : checkPrefixCuts (2^48) 9185263617 10 Manual.Count131072.C070048.packed 64 cuts70048 = true := by
 decide +kernel
def pointBounds70048 : List (Nat × Nat × Nat) := [(9185265664,115822127410388,115822516920539)]
theorem point_links_checked70048 : (cuts70048.take 1).map (fun c => (9185263617-1+2*2^10*c.k,115822124805633+c.lower,115822514315782+c.upper)) = pointBounds70048 := by
 decide +kernel
def cuts70049 : List PrefixCut := [⟨64,174116511,174116618⟩]
theorem checked70049 : checkPrefixCuts (2^48) 9185394689 10 Manual.Count131072.C070049.packed 64 cuts70049 = true := by
 decide +kernel
def cuts70050 : List PrefixCut := [⟨14,39499163,39499184⟩,
⟨64,177852499,177852600⟩]
theorem checked70050 : checkPrefixCuts (2^48) 9185525761 10 Manual.Count131072.C070050.packed 64 cuts70050 = true := by
 decide +kernel
def pointBounds70050 : List (Nat × Nat × Nat) := [(9185554432,115822513551544,115822903061927)]
theorem point_links_checked70050 : (cuts70050.take 1).map (fun c => (9185525761-1+2*2^10*c.k,115822474052381+c.lower,115822863562743+c.upper)) = pointBounds70050 := by
 decide +kernel
def cuts70051 : List PrefixCut := [⟨64,173559974,173560073⟩]
theorem checked70051 : checkPrefixCuts (2^48) 9185656833 10 Manual.Count131072.C070051.packed 64 cuts70051 = true := by
 decide +kernel
def cuts70052 : List PrefixCut := [⟨27,72377207,72377251⟩,
⟨64,171718959,171719066⟩]
theorem checked70052 : checkPrefixCuts (2^48) 9185787905 10 Manual.Count131072.C070052.packed 64 cuts70052 = true := by
 decide +kernel
def pointBounds70052 : List (Nat × Nat × Nat) := [(9185843200,115822897842061,115823287352667)]
theorem point_links_checked70052 : (cuts70052.take 1).map (fun c => (9185787905-1+2*2^10*c.k,115822825464854+c.lower,115823214975416+c.upper)) = pointBounds70052 := by
 decide +kernel
def cuts70053 : List PrefixCut := [⟨64,173616294,173616397⟩]
theorem checked70053 : checkPrefixCuts (2^48) 9185918977 10 Manual.Count131072.C070053.packed 64 cuts70053 = true := by
 decide +kernel
def cuts70054 : List PrefixCut := [⟨40,108286791,108286852⟩,
⟨64,174104096,174104196⟩]
theorem checked70054 : checkPrefixCuts (2^48) 9186050049 10 Manual.Count131072.C070054.packed 64 cuts70054 = true := by
 decide +kernel
def pointBounds70054 : List (Nat × Nat × Nat) := [(9186131968,115823279086898,115823668597731)]
theorem point_links_checked70054 : (cuts70054.take 1).map (fun c => (9186050049-1+2*2^10*c.k,115823170800107+c.lower,115823560310879+c.upper)) = pointBounds70054 := by
 decide +kernel
def cuts70055 : List PrefixCut := [⟨64,174745083,174745181⟩]
theorem checked70055 : checkPrefixCuts (2^48) 9186181121 10 Manual.Count131072.C070055.packed 64 cuts70055 = true := by
 decide +kernel
def cuts70056 : List PrefixCut := [⟨53,147105058,147105145⟩,
⟨64,176519733,176519834⟩]
theorem checked70056 : checkPrefixCuts (2^48) 9186312193 10 Manual.Count131072.C070056.packed 64 cuts70056 = true := by
 decide +kernel
def pointBounds70056 : List (Nat × Nat × Nat) := [(9186420736,115823666754344,115824056265401)]
theorem point_links_checked70056 : (cuts70056.take 1).map (fun c => (9186312193-1+2*2^10*c.k,115823519649286+c.lower,115823909160256+c.upper)) = pointBounds70056 := by
 decide +kernel
def cuts70057 : List PrefixCut := [⟨64,173391925,173392034⟩]
theorem checked70057 : checkPrefixCuts (2^48) 9186443265 10 Manual.Count131072.C070057.packed 64 cuts70057 = true := by
 decide +kernel
def cuts70058 : List PrefixCut := [⟨64,175963192,175963290⟩]
theorem checked70058 : checkPrefixCuts (2^48) 9186574337 10 Manual.Count131072.C070058.packed 64 cuts70058 = true := by
 decide +kernel
def cuts70059 : List PrefixCut := [⟨2,5361889,5361893⟩,
⟨64,177615173,177615280⟩]
theorem checked70059 : checkPrefixCuts (2^48) 9186705409 10 Manual.Count131072.C070059.packed 64 cuts70059 = true := by
 decide +kernel
def pointBounds70059 : List (Nat × Nat × Nat) := [(9186709504,115824050886025,115824440397307)]
theorem point_links_checked70059 : (cuts70059.take 1).map (fun c => (9186705409-1+2*2^10*c.k,115824045524136+c.lower,115824435035414+c.upper)) = pointBounds70059 := by
 decide +kernel
def cuts70060 : List PrefixCut := [⟨64,174671324,174671428⟩]
theorem checked70060 : checkPrefixCuts (2^48) 9186836481 10 Manual.Count131072.C070060.packed 64 cuts70060 = true := by
 decide +kernel
def cuts70061 : List PrefixCut := [⟨15,40473389,40473414⟩,
⟨64,174362453,174362553⟩]
theorem checked70061 : checkPrefixCuts (2^48) 9186967553 10 Manual.Count131072.C070061.packed 64 cuts70061 = true := by
 decide +kernel
def pointBounds70061 : List (Nat × Nat × Nat) := [(9186998272,115824438284022,115824827795536)]
theorem point_links_checked70061 : (cuts70061.take 1).map (fun c => (9186967553-1+2*2^10*c.k,115824397810633+c.lower,115824787322122+c.upper)) = pointBounds70061 := by
 decide +kernel
def cuts70062 : List PrefixCut := [⟨64,175371023,175371121⟩]
theorem checked70062 : checkPrefixCuts (2^48) 9187098625 10 Manual.Count131072.C070062.packed 64 cuts70062 = true := by
 decide +kernel
def cuts70063 : List PrefixCut := [⟨28,74694294,74694341⟩,
⟨64,174020457,174020563⟩]
theorem checked70063 : checkPrefixCuts (2^48) 9187229697 10 Manual.Count131072.C070063.packed 64 cuts70063 = true := by
 decide +kernel
def pointBounds70063 : List (Nat × Nat × Nat) := [(9187287040,115824822238403,115825211750137)]
theorem point_links_checked70063 : (cuts70063.take 1).map (fun c => (9187229697-1+2*2^10*c.k,115824747544109+c.lower,115825137055796+c.upper)) = pointBounds70063 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S8.B000001
