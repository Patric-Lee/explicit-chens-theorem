import PlattAssemblyKernel
import PlattCertificates.Count131072.C060064
import PlattCertificates.Count131072.C060065
import PlattCertificates.Count131072.C060066
import PlattCertificates.Count131072.C060067
import PlattCertificates.Count131072.C060068
import PlattCertificates.Count131072.C060069
import PlattCertificates.Count131072.C060070
import PlattCertificates.Count131072.C060071
import PlattCertificates.Count131072.C060072
import PlattCertificates.Count131072.C060073
import PlattCertificates.Count131072.C060074
import PlattCertificates.Count131072.C060075
import PlattCertificates.Count131072.C060076
import PlattCertificates.Count131072.C060077
import PlattCertificates.Count131072.C060078
import PlattCertificates.Count131072.C060079
import PlattCertificates.Count131072.C060080
import PlattCertificates.Count131072.C060081
import PlattCertificates.Count131072.C060082
import PlattCertificates.Count131072.C060083
import PlattCertificates.Count131072.C060084
import PlattCertificates.Count131072.C060085
import PlattCertificates.Count131072.C060086
import PlattCertificates.Count131072.C060087
import PlattCertificates.Count131072.C060088
import PlattCertificates.Count131072.C060089
import PlattCertificates.Count131072.C060090
import PlattCertificates.Count131072.C060091
import PlattCertificates.Count131072.C060092
import PlattCertificates.Count131072.C060093
import PlattCertificates.Count131072.C060094
import PlattCertificates.Count131072.C060095
namespace ChenEffective.PlattWindow.Assembly.Prefix.S7.B000002
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts60064 : List PrefixCut := [⟨64,204869323,204869442⟩]
theorem checked60064 : checkPrefixCuts (2^48) 7876640769 10 Manual.Count131072.C060064.packed 64 cuts60064 = true := by
 decide +kernel
def cuts60065 : List PrefixCut := [⟨9,29266770,29266787⟩,
⟨64,206759857,206759974⟩]
theorem checked60065 : checkPrefixCuts (2^48) 7876771841 10 Manual.Count131072.C060065.packed 64 cuts60065 = true := by
 decide +kernel
def pointBounds60065 : List (Nat × Nat × Nat) := [(7876790272,113930191496614,113930579911495)]
theorem point_links_checked60065 : (cuts60065.take 1).map (fun c => (7876771841-1+2*2^10*c.k,113930162229844+c.lower,113930550644708+c.upper)) = pointBounds60065 := by
 decide +kernel
def cuts60066 : List PrefixCut := [⟨64,204290761,204290881⟩]
theorem checked60066 : checkPrefixCuts (2^48) 7876902913 10 Manual.Count131072.C060066.packed 64 cuts60066 = true := by
 decide +kernel
def cuts60067 : List PrefixCut := [⟨2,7182455,7182459⟩,
⟨64,204716183,204716302⟩]
theorem checked60067 : checkPrefixCuts (2^48) 7877033985 10 Manual.Count131072.C060067.packed 64 cuts60067 = true := by
 decide +kernel
def pointBounds60067 : List (Nat × Nat × Nat) := [(7877038080,113930580462917,113930968878022)]
theorem point_links_checked60067 : (cuts60067.take 1).map (fun c => (7877033985-1+2*2^10*c.k,113930573280462+c.lower,113930961695563+c.upper)) = pointBounds60067 := by
 decide +kernel
def cuts60068 : List PrefixCut := [⟨59,188061433,188061544⟩,
⟨64,203176258,203176379⟩]
theorem checked60068 : checkPrefixCuts (2^48) 7877165057 10 Manual.Count131072.C060068.packed 64 cuts60068 = true := by
 decide +kernel
def pointBounds60068 : List (Nat × Nat × Nat) := [(7877285888,113930966058078,113931354473409)]
theorem point_links_checked60068 : (cuts60068.take 1).map (fun c => (7877165057-1+2*2^10*c.k,113930777996645+c.lower,113931166411865+c.upper)) = pointBounds60068 := by
 decide +kernel
def cuts60069 : List PrefixCut := [⟨64,203673119,203673240⟩]
theorem checked60069 : checkPrefixCuts (2^48) 7877296129 10 Manual.Count131072.C060069.packed 64 cuts60069 = true := by
 decide +kernel
def cuts60070 : List PrefixCut := [⟨52,165365797,165365891⟩,
⟨64,203919862,203919975⟩]
theorem checked60070 : checkPrefixCuts (2^48) 7877427201 10 Manual.Count131072.C060070.packed 64 cuts60070 = true := by
 decide +kernel
def pointBounds60070 : List (Nat × Nat × Nat) := [(7877533696,113931350211819,113931738627375)]
theorem point_links_checked60070 : (cuts60070.take 1).map (fun c => (7877427201-1+2*2^10*c.k,113931184846022+c.lower,113931573261484+c.upper)) = pointBounds60070 := by
 decide +kernel
def cuts60071 : List PrefixCut := [⟨64,202380033,202380148⟩]
theorem checked60071 : checkPrefixCuts (2^48) 7877558273 10 Manual.Count131072.C060071.packed 64 cuts60071 = true := by
 decide +kernel
def cuts60072 : List PrefixCut := [⟨45,144386675,144386757⟩,
⟨64,205628128,205628246⟩]
theorem checked60072 : checkPrefixCuts (2^48) 7877689345 10 Manual.Count131072.C060072.packed 64 cuts60072 = true := by
 decide +kernel
def pointBounds60072 : List (Nat × Nat × Nat) := [(7877781504,113931735532592,113932123948364)]
theorem point_links_checked60072 : (cuts60072.take 1).map (fun c => (7877689345-1+2*2^10*c.k,113931591145917+c.lower,113931979561607+c.upper)) = pointBounds60072 := by
 decide +kernel
def cuts60073 : List PrefixCut := [⟨64,203087916,203088028⟩]
theorem checked60073 : checkPrefixCuts (2^48) 7877820417 10 Manual.Count131072.C060073.packed 64 cuts60073 = true := by
 decide +kernel
def cuts60074 : List PrefixCut := [⟨38,122408504,122408571⟩,
⟨64,205228271,205228385⟩]
theorem checked60074 : checkPrefixCuts (2^48) 7877951489 10 Manual.Count131072.C060074.packed 64 cuts60074 = true := by
 decide +kernel
def pointBounds60074 : List (Nat × Nat × Nat) := [(7878029312,113932122270465,113932510686452)]
theorem point_links_checked60074 : (cuts60074.take 1).map (fun c => (7877951489-1+2*2^10*c.k,113931999861961+c.lower,113932388277881+c.upper)) = pointBounds60074 := by
 decide +kernel
def cuts60075 : List PrefixCut := [⟨64,206082335,206082455⟩]
theorem checked60075 : checkPrefixCuts (2^48) 7878082561 10 Manual.Count131072.C060075.packed 64 cuts60075 = true := by
 decide +kernel
def cuts60076 : List PrefixCut := [⟨31,99216993,99217050⟩,
⟨64,205936001,205936117⟩]
theorem checked60076 : checkPrefixCuts (2^48) 7878213633 10 Manual.Count131072.C060076.packed 64 cuts60076 = true := by
 decide +kernel
def pointBounds60076 : List (Nat × Nat × Nat) := [(7878277120,113932510389560,113932898805771)]
theorem point_links_checked60076 : (cuts60076.take 1).map (fun c => (7878213633-1+2*2^10*c.k,113932411172567+c.lower,113932799588721+c.upper)) = pointBounds60076 := by
 decide +kernel
def cuts60077 : List PrefixCut := [⟨64,205682487,205682603⟩]
theorem checked60077 : checkPrefixCuts (2^48) 7878344705 10 Manual.Count131072.C060077.packed 64 cuts60077 = true := by
 decide +kernel
def cuts60078 : List PrefixCut := [⟨24,78063413,78063456⟩,
⟨64,205250340,205250458⟩]
theorem checked60078 : checkPrefixCuts (2^48) 7878475777 10 Manual.Count131072.C060078.packed 64 cuts60078 = true := by
 decide +kernel
def pointBounds60078 : List (Nat × Nat × Nat) := [(7878524928,113932900854468,113933289270897)]
theorem point_links_checked60078 : (cuts60078.take 1).map (fun c => (7878475777-1+2*2^10*c.k,113932822791055+c.lower,113933211207441+c.upper)) = pointBounds60078 := by
 decide +kernel
def cuts60079 : List PrefixCut := [⟨64,208640899,208641016⟩]
theorem checked60079 : checkPrefixCuts (2^48) 7878606849 10 Manual.Count131072.C060079.packed 64 cuts60079 = true := by
 decide +kernel
def cuts60080 : List PrefixCut := [⟨17,52481212,52481242⟩,
⟨64,201313684,201313800⟩]
theorem checked60080 : checkPrefixCuts (2^48) 7878737921 10 Manual.Count131072.C060080.packed 64 cuts60080 = true := by
 decide +kernel
def pointBounds60080 : List (Nat × Nat × Nat) := [(7878772736,113933289163506,113933677580157)]
theorem point_links_checked60080 : (cuts60080.take 1).map (fun c => (7878737921-1+2*2^10*c.k,113933236682294+c.lower,113933625098915+c.upper)) = pointBounds60080 := by
 decide +kernel
def cuts60081 : List PrefixCut := [⟨64,204061167,204061289⟩]
theorem checked60081 : checkPrefixCuts (2^48) 7878868993 10 Manual.Count131072.C060081.packed 64 cuts60081 = true := by
 decide +kernel
def cuts60082 : List PrefixCut := [⟨10,31616318,31616334⟩,
⟨64,203843440,203843549⟩]
theorem checked60082 : checkPrefixCuts (2^48) 7879000065 10 Manual.Count131072.C060082.packed 64 cuts60082 = true := by
 decide +kernel
def pointBounds60082 : List (Nat × Nat × Nat) := [(7879020544,113933673673463,113934062090338)]
theorem point_links_checked60082 : (cuts60082.take 1).map (fun c => (7879000065-1+2*2^10*c.k,113933642057145+c.lower,113934030474004+c.upper)) = pointBounds60082 := by
 decide +kernel
def cuts60083 : List PrefixCut := [⟨64,207340967,207341082⟩]
theorem checked60083 : checkPrefixCuts (2^48) 7879131137 10 Manual.Count131072.C060083.packed 64 cuts60083 = true := by
 decide +kernel
def cuts60084 : List PrefixCut := [⟨3,9681068,9681073⟩,
⟨64,200764454,200764568⟩]
theorem checked60084 : checkPrefixCuts (2^48) 7879262209 10 Manual.Count131072.C060084.packed 64 cuts60084 = true := by
 decide +kernel
def pointBounds60084 : List (Nat × Nat × Nat) := [(7879268352,113934062922620,113934451339708)]
theorem point_links_checked60084 : (cuts60084.take 1).map (fun c => (7879262209-1+2*2^10*c.k,113934053241552+c.lower,113934441658635+c.upper)) = pointBounds60084 := by
 decide +kernel
def cuts60085 : List PrefixCut := [⟨60,195009859,195009970⟩,
⟨64,208084235,208084354⟩]
theorem checked60085 : checkPrefixCuts (2^48) 7879393281 10 Manual.Count131072.C060085.packed 64 cuts60085 = true := by
 decide +kernel
def pointBounds60085 : List (Nat × Nat × Nat) := [(7879516160,113934449015865,113934837433173)]
theorem point_links_checked60085 : (cuts60085.take 1).map (fun c => (7879393281-1+2*2^10*c.k,113934254006006+c.lower,113934642423203+c.upper)) = pointBounds60085 := by
 decide +kernel
def cuts60086 : List PrefixCut := [⟨64,205937471,205937584⟩]
theorem checked60086 : checkPrefixCuts (2^48) 7879524353 10 Manual.Count131072.C060086.packed 64 cuts60086 = true := by
 decide +kernel
def cuts60087 : List PrefixCut := [⟨53,170105694,170105788⟩,
⟨64,206041205,206041318⟩]
theorem checked60087 : checkPrefixCuts (2^48) 7879655425 10 Manual.Count131072.C060087.packed 64 cuts60087 = true := by
 decide +kernel
def pointBounds60087 : List (Nat × Nat × Nat) := [(7879763968,113934838133406,113935226550929)]
theorem point_links_checked60087 : (cuts60087.take 1).map (fun c => (7879655425-1+2*2^10*c.k,113934668027712+c.lower,113935056445141+c.upper)) = pointBounds60087 := by
 decide +kernel
def cuts60088 : List PrefixCut := [⟨64,206573591,206573712⟩]
theorem checked60088 : checkPrefixCuts (2^48) 7879786497 10 Manual.Count131072.C060088.packed 64 cuts60088 = true := by
 decide +kernel
def cuts60089 : List PrefixCut := [⟨46,148667988,148668069⟩,
⟨64,205748590,205748702⟩]
theorem checked60089 : checkPrefixCuts (2^48) 7879917569 10 Manual.Count131072.C060089.packed 64 cuts60089 = true := by
 decide +kernel
def pointBounds60089 : List (Nat × Nat × Nat) := [(7880011776,113935229310496,113935617728240)]
theorem point_links_checked60089 : (cuts60089.take 1).map (fun c => (7879917569-1+2*2^10*c.k,113935080642508+c.lower,113935469060171+c.upper)) = pointBounds60089 := by
 decide +kernel
def cuts60090 : List PrefixCut := [⟨64,205280804,205280923⟩]
theorem checked60090 : checkPrefixCuts (2^48) 7880048641 10 Manual.Count131072.C060090.packed 64 cuts60090 = true := by
 decide +kernel
def cuts60091 : List PrefixCut := [⟨39,125588601,125588670⟩,
⟨64,204920217,204920328⟩]
theorem checked60091 : checkPrefixCuts (2^48) 7880179713 10 Manual.Count131072.C060091.packed 64 cuts60091 = true := by
 decide +kernel
def pointBounds60091 : List (Nat × Nat × Nat) := [(7880259584,113935617260503,113936005678466)]
theorem point_links_checked60091 : (cuts60091.take 1).map (fun c => (7880179713-1+2*2^10*c.k,113935491671902+c.lower,113935880089796+c.upper)) = pointBounds60091 := by
 decide +kernel
def cuts60092 : List PrefixCut := [⟨64,205666888,205667005⟩]
theorem checked60092 : checkPrefixCuts (2^48) 7880310785 10 Manual.Count131072.C060092.packed 64 cuts60092 = true := by
 decide +kernel
def cuts60093 : List PrefixCut := [⟨32,100939102,100939157⟩,
⟨64,205413423,205413534⟩]
theorem checked60093 : checkPrefixCuts (2^48) 7880441857 10 Manual.Count131072.C060093.packed 64 cuts60093 = true := by
 decide +kernel
def pointBounds60093 : List (Nat × Nat × Nat) := [(7880507392,113936003198109,113936391616286)]
theorem point_links_checked60093 : (cuts60093.take 1).map (fun c => (7880441857-1+2*2^10*c.k,113935902259007+c.lower,113936290677129+c.upper)) = pointBounds60093 := by
 decide +kernel
def cuts60094 : List PrefixCut := [⟨64,201945438,201945554⟩]
theorem checked60094 : checkPrefixCuts (2^48) 7880572929 10 Manual.Count131072.C060094.packed 64 cuts60094 = true := by
 decide +kernel
def cuts60095 : List PrefixCut := [⟨25,80755815,80755859⟩,
⟨64,205835198,205835314⟩]
theorem checked60095 : checkPrefixCuts (2^48) 7880704001 10 Manual.Count131072.C060095.packed 64 cuts60095 = true := by
 decide +kernel
def pointBounds60095 : List (Nat × Nat × Nat) := [(7880755200,113936390373683,113936778792076)]
theorem point_links_checked60095 : (cuts60095.take 1).map (fun c => (7880704001-1+2*2^10*c.k,113936309617868+c.lower,113936698036217+c.upper)) = pointBounds60095 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S7.B000002
