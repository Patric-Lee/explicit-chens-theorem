import PlattAssemblyKernel
import PlattCertificates.Count131072.C030896
import PlattCertificates.Count131072.C030897
import PlattCertificates.Count131072.C030898
import PlattCertificates.Count131072.C030899
import PlattCertificates.Count131072.C030900
import PlattCertificates.Count131072.C030901
import PlattCertificates.Count131072.C030902
import PlattCertificates.Count131072.C030903
import PlattCertificates.Count131072.C030904
import PlattCertificates.Count131072.C030905
import PlattCertificates.Count131072.C030906
import PlattCertificates.Count131072.C030907
import PlattCertificates.Count131072.C030908
import PlattCertificates.Count131072.C030909
import PlattCertificates.Count131072.C030910
import PlattCertificates.Count131072.C030911
import PlattCertificates.Count131072.C030912
import PlattCertificates.Count131072.C030913
import PlattCertificates.Count131072.C030914
import PlattCertificates.Count131072.C030915
import PlattCertificates.Count131072.C030916
import PlattCertificates.Count131072.C030917
import PlattCertificates.Count131072.C030918
import PlattCertificates.Count131072.C030919
import PlattCertificates.Count131072.C030920
import PlattCertificates.Count131072.C030921
import PlattCertificates.Count131072.C030922
import PlattCertificates.Count131072.C030923
import PlattCertificates.Count131072.C030924
import PlattCertificates.Count131072.C030925
import PlattCertificates.Count131072.C030926
import PlattCertificates.Count131072.C030927
namespace ChenEffective.PlattWindow.Assembly.Prefix.S4.B000028
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts30896 : List PrefixCut := [⟨19,62078680,62078715⟩,
⟨128,414754826,414755061⟩]
theorem checked30896 : checkPrefixCuts (2^48) 4053532673 9 Manual.Count131072.C030896.packed 128 cuts30896 = true := by
 decide +kernel
def pointBounds30896 : List (Nat × Nat × Nat) := [(4053552128,105602307588297,105602691120016)]
theorem point_links_checked30896 : (cuts30896.take 1).map (fun c => (4053532673-1+2*2^9*c.k,105602245509617+c.lower,105602629041301+c.upper)) = pointBounds30896 := by
 decide +kernel
def cuts30897 : List PrefixCut := [⟨15,48119858,48119888⟩,
⟨128,412797225,412797460⟩]
theorem checked30897 : checkPrefixCuts (2^48) 4053663745 9 Manual.Count131072.C030897.packed 128 cuts30897 = true := by
 decide +kernel
def pointBounds30897 : List (Nat × Nat × Nat) := [(4053679104,105602708384301,105603091916250)]
theorem point_links_checked30897 : (cuts30897.take 1).map (fun c => (4053663745-1+2*2^9*c.k,105602660264443+c.lower,105603043796362+c.upper)) = pointBounds30897 := by
 decide +kernel
def cuts30898 : List PrefixCut := [⟨11,37703107,37703128⟩,
⟨128,411187005,411187234⟩]
theorem checked30898 : checkPrefixCuts (2^48) 4053794817 9 Manual.Count131072.C030898.packed 128 cuts30898 = true := by
 decide +kernel
def pointBounds30898 : List (Nat × Nat × Nat) := [(4053806080,105603110764775,105603494296950)]
theorem point_links_checked30898 : (cuts30898.take 1).map (fun c => (4053794817-1+2*2^9*c.k,105603073061668+c.lower,105603456593822+c.upper)) = pointBounds30898 := by
 decide +kernel
def cuts30899 : List PrefixCut := [⟨7,22912760,22912773⟩,
⟨128,409507291,409507521⟩]
theorem checked30899 : checkPrefixCuts (2^48) 4053925889 9 Manual.Count131072.C030899.packed 128 cuts30899 = true := by
 decide +kernel
def pointBounds30899 : List (Nat × Nat × Nat) := [(4053933056,105603507161433,105603890693829)]
theorem point_links_checked30899 : (cuts30899.take 1).map (fun c => (4053925889-1+2*2^9*c.k,105603484248673+c.lower,105603867781056+c.upper)) = pointBounds30899 := by
 decide +kernel
def cuts30900 : List PrefixCut := [⟨3,9997978,9997983⟩,
⟨127,404981208,404981436⟩,
⟨128,407966620,407966850⟩]
theorem checked30900 : checkPrefixCuts (2^48) 4054056961 9 Manual.Count131072.C030900.packed 128 cuts30900 = true := by
 decide +kernel
def pointBounds30900 : List (Nat × Nat × Nat) := [(4054060032,105603903753942,105604287286560),(4054187008,105604298737172,105604682270013)]
theorem point_links_checked30900 : (cuts30900.take 2).map (fun c => (4054056961-1+2*2^9*c.k,105603893755964+c.lower,105604277288577+c.upper)) = pointBounds30900 := by
 decide +kernel
def cuts30901 : List PrefixCut := [⟨123,396984098,396984325⟩,
⟨128,412396664,412396901⟩]
theorem checked30901 : checkPrefixCuts (2^48) 4054188033 9 Manual.Count131072.C030901.packed 128 cuts30901 = true := by
 decide +kernel
def pointBounds30901 : List (Nat × Nat × Nat) := [(4054313984,105604698706682,105605082239752)]
theorem point_links_checked30901 : (cuts30901.take 1).map (fun c => (4054188033-1+2*2^9*c.k,105604301722584+c.lower,105604685255427+c.upper)) = pointBounds30901 := by
 decide +kernel
def cuts30902 : List PrefixCut := [⟨119,379129355,379129565⟩,
⟨128,406829439,406829664⟩]
theorem checked30902 : checkPrefixCuts (2^48) 4054319105 9 Manual.Count131072.C030902.packed 128 cuts30902 = true := by
 decide +kernel
def pointBounds30902 : List (Nat × Nat × Nat) := [(4054440960,105605093248603,105605476781893)]
theorem point_links_checked30902 : (cuts30902.take 1).map (fun c => (4054319105-1+2*2^9*c.k,105604714119248+c.lower,105605097652328+c.upper)) = pointBounds30902 := by
 decide +kernel
def cuts30903 : List PrefixCut := [⟨115,371064270,371064479⟩,
⟨128,412161831,412162065⟩]
theorem checked30903 : checkPrefixCuts (2^48) 4054450177 9 Manual.Count131072.C030903.packed 128 cuts30903 = true := by
 decide +kernel
def pointBounds30903 : List (Nat × Nat × Nat) := [(4054567936,105605492012957,105605875546471)]
theorem point_links_checked30903 : (cuts30903.take 1).map (fun c => (4054450177-1+2*2^9*c.k,105605120948687+c.lower,105605504481992+c.upper)) = pointBounds30903 := by
 decide +kernel
def cuts30904 : List PrefixCut := [⟨111,358556778,358556978⟩,
⟨128,413467485,413467716⟩]
theorem checked30904 : checkPrefixCuts (2^48) 4054581249 9 Manual.Count131072.C030904.packed 128 cuts30904 = true := by
 decide +kernel
def pointBounds30904 : List (Nat × Nat × Nat) := [(4054694912,105605891667296,105606275201035)]
theorem point_links_checked30904 : (cuts30904.take 1).map (fun c => (4054581249-1+2*2^9*c.k,105605533110518+c.lower,105605916644057+c.upper)) = pointBounds30904 := by
 decide +kernel
def cuts30905 : List PrefixCut := [⟨107,345980652,345980838⟩,
⟨128,412551690,412551913⟩]
theorem checked30905 : checkPrefixCuts (2^48) 4054712321 9 Manual.Count131072.C030905.packed 128 cuts30905 = true := by
 decide +kernel
def pointBounds30905 : List (Nat × Nat × Nat) := [(4054821888,105606292558655,105606676092611)]
theorem point_links_checked30905 : (cuts30905.take 1).map (fun c => (4054712321-1+2*2^9*c.k,105605946578003+c.lower,105606330111773+c.upper)) = pointBounds30905 := by
 decide +kernel
def cuts30906 : List PrefixCut := [⟨103,332433478,332433668⟩,
⟨128,414273685,414273919⟩]
theorem checked30906 : checkPrefixCuts (2^48) 4054843393 9 Manual.Count131072.C030906.packed 128 cuts30906 = true := by
 decide +kernel
def pointBounds30906 : List (Nat × Nat × Nat) := [(4054948864,105606691563171,105607075097354)]
theorem point_links_checked30906 : (cuts30906.take 1).map (fun c => (4054843393-1+2*2^9*c.k,105606359129693+c.lower,105606742663686+c.upper)) = pointBounds30906 := by
 decide +kernel
def cuts30907 : List PrefixCut := [⟨99,323954405,323954583⟩,
⟨128,414954491,414954718⟩]
theorem checked30907 : checkPrefixCuts (2^48) 4054974465 9 Manual.Count131072.C030907.packed 128 cuts30907 = true := by
 decide +kernel
def pointBounds30907 : List (Nat × Nat × Nat) := [(4055075840,105607097357783,105607480892188)]
theorem point_links_checked30907 : (cuts30907.take 1).map (fun c => (4054974465-1+2*2^9*c.k,105606773403378+c.lower,105607156937605+c.upper)) = pointBounds30907 := by
 decide +kernel
def cuts30908 : List PrefixCut := [⟨95,306521788,306521957⟩,
⟨128,409943460,409943686⟩]
theorem checked30908 : checkPrefixCuts (2^48) 4055105537 9 Manual.Count131072.C030908.packed 128 cuts30908 = true := by
 decide +kernel
def pointBounds30908 : List (Nat × Nat × Nat) := [(4055202816,105607494879657,105607878414280)]
theorem point_links_checked30908 : (cuts30908.take 1).map (fun c => (4055105537-1+2*2^9*c.k,105607188357869+c.lower,105607571892323+c.upper)) = pointBounds30908 := by
 decide +kernel
def cuts30909 : List PrefixCut := [⟨91,296725294,296725462⟩,
⟨128,415691137,415691375⟩]
theorem checked30909 : checkPrefixCuts (2^48) 4055236609 9 Manual.Count131072.C030909.packed 128 cuts30909 = true := by
 decide +kernel
def pointBounds30909 : List (Nat × Nat × Nat) := [(4055329792,105607895026623,105608278561471)]
theorem point_links_checked30909 : (cuts30909.take 1).map (fun c => (4055236609-1+2*2^9*c.k,105607598301329+c.lower,105607981836009+c.upper)) = pointBounds30909 := by
 decide +kernel
def cuts30910 : List PrefixCut := [⟨87,272423339,272423492⟩,
⟨128,406654740,406654965⟩]
theorem checked30910 : checkPrefixCuts (2^48) 4055367681 9 Manual.Count131072.C030910.packed 128 cuts30910 = true := by
 decide +kernel
def pointBounds30910 : List (Nat × Nat × Nat) := [(4055456768,105608286415805,105608669950876)]
theorem point_links_checked30910 : (cuts30910.take 1).map (fun c => (4055367681-1+2*2^9*c.k,105608013992466+c.lower,105608397527384+c.upper)) = pointBounds30910 := by
 decide +kernel
def cuts30911 : List PrefixCut := [⟨83,269499665,269499814⟩,
⟨128,412055253,412055482⟩]
theorem checked30911 : checkPrefixCuts (2^48) 4055498753 9 Manual.Count131072.C030911.packed 128 cuts30911 = true := by
 decide +kernel
def pointBounds30911 : List (Nat × Nat × Nat) := [(4055583744,105608690146871,105609073682163)]
theorem point_links_checked30911 : (cuts30911.take 1).map (fun c => (4055498753-1+2*2^9*c.k,105608420647206+c.lower,105608804182349+c.upper)) = pointBounds30911 := by
 decide +kernel
def cuts30912 : List PrefixCut := [⟨79,252903825,252903966⟩,
⟨128,412805303,412805534⟩]
theorem checked30912 : checkPrefixCuts (2^48) 4055629825 9 Manual.Count131072.C030912.packed 128 cuts30912 = true := by
 decide +kernel
def pointBounds30912 : List (Nat × Nat × Nat) := [(4055710720,105609085606284,105609469141797)]
theorem point_links_checked30912 : (cuts30912.take 1).map (fun c => (4055629825-1+2*2^9*c.k,105608832702459+c.lower,105609216237831+c.upper)) = pointBounds30912 := by
 decide +kernel
def cuts30913 : List PrefixCut := [⟨75,236725422,236725553⟩,
⟨128,408489106,408489338⟩]
theorem checked30913 : checkPrefixCuts (2^48) 4055760897 9 Manual.Count131072.C030913.packed 128 cuts30913 = true := by
 decide +kernel
def pointBounds30913 : List (Nat × Nat × Nat) := [(4055837696,105609482233184,105609865768918)]
theorem point_links_checked30913 : (cuts30913.take 1).map (fun c => (4055760897-1+2*2^9*c.k,105609245507762+c.lower,105609629043365+c.upper)) = pointBounds30913 := by
 decide +kernel
def cuts30914 : List PrefixCut := [⟨71,227349125,227349255⟩,
⟨128,412292860,412293091⟩]
theorem checked30914 : checkPrefixCuts (2^48) 4055891969 9 Manual.Count131072.C030914.packed 128 cuts30914 = true := by
 decide +kernel
def pointBounds30914 : List (Nat × Nat × Nat) := [(4055964672,105609881345993,105610264881958)]
theorem point_links_checked30914 : (cuts30914.take 1).map (fun c => (4055891969-1+2*2^9*c.k,105609653996868+c.lower,105610037532703+c.upper)) = pointBounds30914 := by
 decide +kernel
def cuts30915 : List PrefixCut := [⟨67,216307888,216308008⟩,
⟨128,415402306,415402538⟩]
theorem checked30915 : checkPrefixCuts (2^48) 4056023041 9 Manual.Count131072.C030915.packed 128 cuts30915 = true := by
 decide +kernel
def pointBounds30915 : List (Nat × Nat × Nat) := [(4056091648,105610282597616,105610666133802)]
theorem point_links_checked30915 : (cuts30915.take 1).map (fun c => (4056023041-1+2*2^9*c.k,105610066289728+c.lower,105610449825794+c.upper)) = pointBounds30915 := by
 decide +kernel
def cuts30916 : List PrefixCut := [⟨63,200479190,200479307⟩,
⟨128,410392587,410392820⟩]
theorem checked30916 : checkPrefixCuts (2^48) 4056154113 9 Manual.Count131072.C030916.packed 128 cuts30916 = true := by
 decide +kernel
def pointBounds30916 : List (Nat × Nat × Nat) := [(4056218624,105610682171224,105611065707639)]
theorem point_links_checked30916 : (cuts30916.take 1).map (fun c => (4056154113-1+2*2^9*c.k,105610481692034+c.lower,105610865228332+c.upper)) = pointBounds30916 := by
 decide +kernel
def cuts30917 : List PrefixCut := [⟨59,187704743,187704849⟩,
⟨128,407117980,407118207⟩]
theorem checked30917 : checkPrefixCuts (2^48) 4056285185 9 Manual.Count131072.C030917.packed 128 cuts30917 = true := by
 decide +kernel
def pointBounds30917 : List (Nat × Nat × Nat) := [(4056345600,105611079789364,105611463326001)]
theorem point_links_checked30917 : (cuts30917.take 1).map (fun c => (4056285185-1+2*2^9*c.k,105610892084621+c.lower,105611275621152+c.upper)) = pointBounds30917 := by
 decide +kernel
def cuts30918 : List PrefixCut := [⟨55,175278030,175278128⟩,
⟨128,414113048,414113283⟩]
theorem checked30918 : checkPrefixCuts (2^48) 4056416257 9 Manual.Count131072.C030918.packed 128 cuts30918 = true := by
 decide +kernel
def pointBounds30918 : List (Nat × Nat × Nat) := [(4056472576,105611474480631,105611858017487)]
theorem point_links_checked30918 : (cuts30918.take 1).map (fun c => (4056416257-1+2*2^9*c.k,105611299202601+c.lower,105611682739359+c.upper)) = pointBounds30918 := by
 decide +kernel
def cuts30919 : List PrefixCut := [⟨51,164656194,164656286⟩,
⟨128,410075298,410075528⟩]
theorem checked30919 : checkPrefixCuts (2^48) 4056547329 9 Manual.Count131072.C030919.packed 128 cuts30919 = true := by
 decide +kernel
def pointBounds30919 : List (Nat × Nat × Nat) := [(4056599552,105611877971843,105612261508928)]
theorem point_links_checked30919 : (cuts30919.take 1).map (fun c => (4056547329-1+2*2^9*c.k,105611713315649+c.lower,105612096852642+c.upper)) = pointBounds30919 := by
 decide +kernel
def cuts30920 : List PrefixCut := [⟨47,151259621,151259709⟩,
⟨128,414155691,414155925⟩]
theorem checked30920 : checkPrefixCuts (2^48) 4056678401 9 Manual.Count131072.C030920.packed 128 cuts30920 = true := by
 decide +kernel
def pointBounds30920 : List (Nat × Nat × Nat) := [(4056726528,105612274650568,105612658187879)]
theorem point_links_checked30920 : (cuts30920.take 1).map (fun c => (4056678401-1+2*2^9*c.k,105612123390947+c.lower,105612506928170+c.upper)) = pointBounds30920 := by
 decide +kernel
def cuts30921 : List PrefixCut := [⟨43,135851808,135851888⟩,
⟨128,411228252,411228486⟩]
theorem checked30921 : checkPrefixCuts (2^48) 4056809473 9 Manual.Count131072.C030921.packed 128 cuts30921 = true := by
 decide +kernel
def pointBounds30921 : List (Nat × Nat × Nat) := [(4056853504,105612673398446,105613056935983)]
theorem point_links_checked30921 : (cuts30921.take 1).map (fun c => (4056809473-1+2*2^9*c.k,105612537546638+c.lower,105612921084095+c.upper)) = pointBounds30921 := by
 decide +kernel
def cuts30922 : List PrefixCut := [⟨39,125509757,125509827⟩,
⟨128,415239030,415239264⟩]
theorem checked30922 : checkPrefixCuts (2^48) 4056940545 9 Manual.Count131072.C030922.packed 128 cuts30922 = true := by
 decide +kernel
def pointBounds30922 : List (Nat × Nat × Nat) := [(4056980480,105613074284647,105613457822408)]
theorem point_links_checked30922 : (cuts30922.take 1).map (fun c => (4056940545-1+2*2^9*c.k,105612948774890+c.lower,105613332312581+c.upper)) = pointBounds30922 := by
 decide +kernel
def cuts30923 : List PrefixCut := [⟨35,110311861,110311921⟩,
⟨128,412866734,412866970⟩]
theorem checked30923 : checkPrefixCuts (2^48) 4057071617 9 Manual.Count131072.C030923.packed 128 cuts30923 = true := by
 decide +kernel
def pointBounds30923 : List (Nat × Nat × Nat) := [(4057107456,105613474325781,105613857863766)]
theorem point_links_checked30923 : (cuts30923.take 1).map (fun c => (4057071617-1+2*2^9*c.k,105613364013920+c.lower,105613747551845+c.upper)) = pointBounds30923 := by
 decide +kernel
def cuts30924 : List PrefixCut := [⟨31,99832529,99832586⟩,
⟨128,405499646,405499874⟩]
theorem checked30924 : checkPrefixCuts (2^48) 4057202689 9 Manual.Count131072.C030924.packed 128 cuts30924 = true := by
 decide +kernel
def pointBounds30924 : List (Nat × Nat × Nat) := [(4057234432,105613876713183,105614260251401)]
theorem point_links_checked30924 : (cuts30924.take 1).map (fun c => (4057202689-1+2*2^9*c.k,105613776880654+c.lower,105614160418815+c.upper)) = pointBounds30924 := by
 decide +kernel
def cuts30925 : List PrefixCut := [⟨27,85746406,85746455⟩,
⟨128,408747078,408747308⟩]
theorem checked30925 : checkPrefixCuts (2^48) 4057333761 9 Manual.Count131072.C030925.packed 128 cuts30925 = true := by
 decide +kernel
def pointBounds30925 : List (Nat × Nat × Nat) := [(4057361408,105614268126706,105614651665144)]
theorem point_links_checked30925 : (cuts30925.take 1).map (fun c => (4057333761-1+2*2^9*c.k,105614182380300+c.lower,105614565918689+c.upper)) = pointBounds30925 := by
 decide +kernel
def cuts30926 : List PrefixCut := [⟨23,75546012,75546051⟩,
⟨128,411716869,411717096⟩]
theorem checked30926 : checkPrefixCuts (2^48) 4057464833 9 Manual.Count131072.C030926.packed 128 cuts30926 = true := by
 decide +kernel
def pointBounds30926 : List (Nat × Nat × Nat) := [(4057488384,105614666673390,105615050212048)]
theorem point_links_checked30926 : (cuts30926.take 1).map (fun c => (4057464833-1+2*2^9*c.k,105614591127378+c.lower,105614974665997+c.upper)) = pointBounds30926 := by
 decide +kernel
def cuts30927 : List PrefixCut := [⟨19,60837235,60837269⟩,
⟨128,409136898,409137130⟩]
theorem checked30927 : checkPrefixCuts (2^48) 4057595905 9 Manual.Count131072.C030927.packed 128 cuts30927 = true := by
 decide +kernel
def pointBounds30927 : List (Nat × Nat × Nat) := [(4057615360,105615063681482,105615447220362)]
theorem point_links_checked30927 : (cuts30927.take 1).map (fun c => (4057595905-1+2*2^9*c.k,105615002844247+c.lower,105615386383093+c.upper)) = pointBounds30927 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S4.B000028
