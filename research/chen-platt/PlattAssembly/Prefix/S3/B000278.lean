import PlattAssemblyKernel
import PlattCertificates.Count131072.C028896
import PlattCertificates.Count131072.C028897
import PlattCertificates.Count131072.C028898
import PlattCertificates.Count131072.C028899
import PlattCertificates.Count131072.C028900
import PlattCertificates.Count131072.C028901
import PlattCertificates.Count131072.C028902
import PlattCertificates.Count131072.C028903
import PlattCertificates.Count131072.C028904
import PlattCertificates.Count131072.C028905
import PlattCertificates.Count131072.C028906
import PlattCertificates.Count131072.C028907
import PlattCertificates.Count131072.C028908
import PlattCertificates.Count131072.C028909
import PlattCertificates.Count131072.C028910
import PlattCertificates.Count131072.C028911
import PlattCertificates.Count131072.C028912
import PlattCertificates.Count131072.C028913
import PlattCertificates.Count131072.C028914
import PlattCertificates.Count131072.C028915
import PlattCertificates.Count131072.C028916
import PlattCertificates.Count131072.C028917
import PlattCertificates.Count131072.C028918
import PlattCertificates.Count131072.C028919
import PlattCertificates.Count131072.C028920
import PlattCertificates.Count131072.C028921
import PlattCertificates.Count131072.C028922
import PlattCertificates.Count131072.C028923
import PlattCertificates.Count131072.C028924
import PlattCertificates.Count131072.C028925
import PlattCertificates.Count131072.C028926
import PlattCertificates.Count131072.C028927
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000278
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts28896 : List PrefixCut := [⟨83,289609191,289609350⟩,
⟨128,442540420,442540666⟩]
theorem checked28896 : checkPrefixCuts (2^48) 3791388673 9 Manual.Count131072.C028896.packed 128 cuts28896 = true := by
 decide +kernel
def pointBounds28896 : List (Nat × Nat × Nat) := [(3791473664,104750713297663,104751096351269)]
theorem point_links_checked28896 : (cuts28896.take 1).map (fun c => (3791388673-1+2*2^9*c.k,104750423688472+c.lower,104750806741919+c.upper)) = pointBounds28896 := by
 decide +kernel
def cuts28897 : List PrefixCut := [⟨71,242087838,242087971⟩,
⟨128,438293632,438293875⟩]
theorem checked28897 : checkPrefixCuts (2^48) 3791519745 9 Manual.Count131072.C028897.packed 128 cuts28897 = true := by
 decide +kernel
def pointBounds28897 : List (Nat × Nat × Nat) := [(3791592448,104751108316730,104751491370556)]
theorem point_links_checked28897 : (cuts28897.take 1).map (fun c => (3791519745-1+2*2^9*c.k,104750866228892+c.lower,104751249282585+c.upper)) = pointBounds28897 := by
 decide +kernel
def cuts28898 : List PrefixCut := [⟨59,208748410,208748526⟩,
⟨128,446667021,446667269⟩]
theorem checked28898 : checkPrefixCuts (2^48) 3791650817 9 Manual.Count131072.C028898.packed 128 cuts28898 = true := by
 decide +kernel
def pointBounds28898 : List (Nat × Nat × Nat) := [(3791711232,104751513270934,104751896324986)]
theorem point_links_checked28898 : (cuts28898.take 1).map (fun c => (3791650817-1+2*2^9*c.k,104751304522524+c.lower,104751687576460+c.upper)) = pointBounds28898 := by
 decide +kernel
def cuts28899 : List PrefixCut := [⟨47,165612514,165612608⟩,
⟨128,441752302,441752551⟩]
theorem checked28899 : checkPrefixCuts (2^48) 3791781889 9 Manual.Count131072.C028899.packed 128 cuts28899 = true := by
 decide +kernel
def pointBounds28899 : List (Nat × Nat × Nat) := [(3791830016,104751916802059,104752299856337)]
theorem point_links_checked28899 : (cuts28899.take 1).map (fun c => (3791781889-1+2*2^9*c.k,104751751189545+c.lower,104752134243729+c.upper)) = pointBounds28899 := by
 decide +kernel
def cuts28900 : List PrefixCut := [⟨35,123444427,123444499⟩,
⟨128,434759529,434759781⟩]
theorem checked28900 : checkPrefixCuts (2^48) 3791912961 9 Manual.Count131072.C028900.packed 128 cuts28900 = true := by
 decide +kernel
def pointBounds28900 : List (Nat × Nat × Nat) := [(3791948800,104752316386274,104752699440779)]
theorem point_links_checked28900 : (cuts28900.take 1).map (fun c => (3791912961-1+2*2^9*c.k,104752192941847+c.lower,104752575996280+c.upper)) = pointBounds28900 := by
 decide +kernel
def cuts28901 : List PrefixCut := [⟨23,76305885,76305926⟩,
⟨128,438975282,438975525⟩]
theorem checked28901 : checkPrefixCuts (2^48) 3792044033 9 Manual.Count131072.C028901.packed 128 cuts28901 = true := by
 decide +kernel
def pointBounds28901 : List (Nat × Nat × Nat) := [(3792067584,104752704007261,104753087061987)]
theorem point_links_checked28901 : (cuts28901.take 1).map (fun c => (3792044033-1+2*2^9*c.k,104752627701376+c.lower,104753010756061+c.upper)) = pointBounds28901 := by
 decide +kernel
def cuts28902 : List PrefixCut := [⟨11,38448592,38448613⟩,
⟨127,438811797,438812046⟩,
⟨128,442597151,442597402⟩]
theorem checked28902 : checkPrefixCuts (2^48) 3792175105 9 Manual.Count131072.C028902.packed 128 cuts28902 = true := by
 decide +kernel
def pointBounds28902 : List (Nat × Nat × Nat) := [(3792186368,104753105125250,104753488180199),(3792305152,104753505488455,104753888543632)]
theorem point_links_checked28902 : (cuts28902.take 2).map (fun c => (3792175105-1+2*2^9*c.k,104753066676658+c.lower,104753449731586+c.upper)) = pointBounds28902 := by
 decide +kernel
def cuts28903 : List PrefixCut := [⟨115,396416880,396417097⟩,
⟨128,442284953,442285196⟩]
theorem checked28903 : checkPrefixCuts (2^48) 3792306177 9 Manual.Count131072.C028903.packed 128 cuts28903 = true := by
 decide +kernel
def pointBounds28903 : List (Nat × Nat × Nat) := [(3792423936,104753905690689,104754288746085)]
theorem point_links_checked28903 : (cuts28903.take 1).map (fun c => (3792306177-1+2*2^9*c.k,104753509273809+c.lower,104753892328988+c.upper)) = pointBounds28903 := by
 decide +kernel
def cuts28904 : List PrefixCut := [⟨103,352837210,352837403⟩,
⟨128,439746181,439746422⟩]
theorem checked28904 : checkPrefixCuts (2^48) 3792437249 9 Manual.Count131072.C028904.packed 128 cuts28904 = true := by
 decide +kernel
def pointBounds28904 : List (Nat × Nat × Nat) := [(3792542720,104754304395972,104754687451587)]
theorem point_links_checked28904 : (cuts28904.take 1).map (fun c => (3792437249-1+2*2^9*c.k,104753951558762+c.lower,104754334614184+c.upper)) = pointBounds28904 := by
 decide +kernel
def cuts28905 : List PrefixCut := [⟨91,310596361,310596536⟩,
⟨128,439508328,439508578⟩]
theorem checked28905 : checkPrefixCuts (2^48) 3792568321 9 Manual.Count131072.C028905.packed 128 cuts28905 = true := by
 decide +kernel
def pointBounds28905 : List (Nat × Nat × Nat) := [(3792661504,104754701901304,104755084957142)]
theorem point_links_checked28905 : (cuts28905.take 1).map (fun c => (3792568321-1+2*2^9*c.k,104754391304943+c.lower,104754774360606+c.upper)) = pointBounds28905 := by
 decide +kernel
def cuts28906 : List PrefixCut := [⟨79,269991026,269991175⟩,
⟨128,436005173,436005413⟩]
theorem checked28906 : checkPrefixCuts (2^48) 3792699393 9 Manual.Count131072.C028906.packed 128 cuts28906 = true := by
 decide +kernel
def pointBounds28906 : List (Nat × Nat × Nat) := [(3792780288,104755100804297,104755483860359)]
theorem point_links_checked28906 : (cuts28906.take 1).map (fun c => (3792699393-1+2*2^9*c.k,104754830813271+c.lower,104755213869184+c.upper)) = pointBounds28906 := by
 decide +kernel
def cuts28907 : List PrefixCut := [⟨67,230204661,230204790⟩,
⟨128,439403784,439404031⟩]
theorem checked28907 : checkPrefixCuts (2^48) 3792830465 9 Manual.Count131072.C028907.packed 128 cuts28907 = true := by
 decide +kernel
def pointBounds28907 : List (Nat × Nat × Nat) := [(3792899072,104755497023105,104755880079387)]
theorem point_links_checked28907 : (cuts28907.take 1).map (fun c => (3792830465-1+2*2^9*c.k,104755266818444+c.lower,104755649874597+c.upper)) = pointBounds28907 := by
 decide +kernel
def cuts28908 : List PrefixCut := [⟨55,192127740,192127846⟩,
⟨128,441466472,441466718⟩]
theorem checked28908 : checkPrefixCuts (2^48) 3792961537 9 Manual.Count131072.C028908.packed 128 cuts28908 = true := by
 decide +kernel
def pointBounds28908 : List (Nat × Nat × Nat) := [(3793017856,104755898349968,104756281406474)]
theorem point_links_checked28908 : (cuts28908.take 1).map (fun c => (3792961537-1+2*2^9*c.k,104755706222228+c.lower,104756089278628+c.upper)) = pointBounds28908 := by
 decide +kernel
def cuts28909 : List PrefixCut := [⟨43,150342970,150343056⟩,
⟨128,441005980,441006231⟩]
theorem checked28909 : checkPrefixCuts (2^48) 3793092609 9 Manual.Count131072.C028909.packed 128 cuts28909 = true := by
 decide +kernel
def pointBounds28909 : List (Nat × Nat × Nat) := [(3793136640,104756298031670,104756681088402)]
theorem point_links_checked28909 : (cuts28909.take 1).map (fun c => (3793092609-1+2*2^9*c.k,104756147688700+c.lower,104756530745346+c.upper)) = pointBounds28909 := by
 decide +kernel
def cuts28910 : List PrefixCut := [⟨31,105147568,105147629⟩,
⟨128,440990704,440990955⟩]
theorem checked28910 : checkPrefixCuts (2^48) 3793223681 9 Manual.Count131072.C028910.packed 128 cuts28910 = true := by
 decide +kernel
def pointBounds28910 : List (Nat × Nat × Nat) := [(3793255424,104756693842248,104757076899206)]
theorem point_links_checked28910 : (cuts28910.take 1).map (fun c => (3793223681-1+2*2^9*c.k,104756588694680+c.lower,104756971751577+c.upper)) = pointBounds28910 := by
 decide +kernel
def cuts28911 : List PrefixCut := [⟨19,67004324,67004362⟩,
⟨128,446688941,446689191⟩]
theorem checked28911 : checkPrefixCuts (2^48) 3793354753 9 Manual.Count131072.C028911.packed 128 cuts28911 = true := by
 decide +kernel
def pointBounds28911 : List (Nat × Nat × Nat) := [(3793374208,104757096689708,104757479746894)]
theorem point_links_checked28911 : (cuts28911.take 1).map (fun c => (3793354753-1+2*2^9*c.k,104757029685384+c.lower,104757412742532+c.upper)) = pointBounds28911 := by
 decide +kernel
def cuts28912 : List PrefixCut := [⟨7,23224432,23224445⟩,
⟨123,424785307,424785540⟩,
⟨128,441479637,441479880⟩]
theorem checked28912 : checkPrefixCuts (2^48) 3793485825 9 Manual.Count131072.C028912.packed 128 cuts28912 = true := by
 decide +kernel
def pointBounds28912 : List (Nat × Nat × Nat) := [(3793492992,104757499598757,104757882656168),(3793611776,104757901159632,104758284217263)]
theorem point_links_checked28912 : (cuts28912.take 2).map (fun c => (3793485825-1+2*2^9*c.k,104757476374325+c.lower,104757859431723+c.upper)) = pointBounds28912 := by
 decide +kernel
def cuts28913 : List PrefixCut := [⟨111,384111938,384112154⟩,
⟨128,445025692,445025941⟩]
theorem checked28913 : checkPrefixCuts (2^48) 3793616897 9 Manual.Count131072.C028913.packed 128 cuts28913 = true := by
 decide +kernel
def pointBounds28913 : List (Nat × Nat × Nat) := [(3793730560,104758301965900,104758685023757)]
theorem point_links_checked28913 : (cuts28913.take 1).map (fun c => (3793616897-1+2*2^9*c.k,104757917853962+c.lower,104758300911603+c.upper)) = pointBounds28913 := by
 decide +kernel
def cuts28914 : List PrefixCut := [⟨99,340251018,340251201⟩,
⟨128,439594285,439594521⟩]
theorem checked28914 : checkPrefixCuts (2^48) 3793747969 9 Manual.Count131072.C028914.packed 128 cuts28914 = true := by
 decide +kernel
def pointBounds28914 : List (Nat × Nat × Nat) := [(3793849344,104758703130672,104759086188745)]
theorem point_links_checked28914 : (cuts28914.take 1).map (fun c => (3793747969-1+2*2^9*c.k,104758362879654+c.lower,104758745937544+c.upper)) = pointBounds28914 := by
 decide +kernel
def cuts28915 : List PrefixCut := [⟨87,301363757,301363927⟩,
⟨128,441211338,441211589⟩]
theorem checked28915 : checkPrefixCuts (2^48) 3793879041 9 Manual.Count131072.C028915.packed 128 cuts28915 = true := by
 decide +kernel
def pointBounds28915 : List (Nat × Nat × Nat) := [(3793968128,104759103837696,104759486895992)]
theorem point_links_checked28915 : (cuts28915.take 1).map (fun c => (3793879041-1+2*2^9*c.k,104758802473939+c.lower,104759185532065+c.upper)) = pointBounds28915 := by
 decide +kernel
def cuts28916 : List PrefixCut := [⟨75,257063273,257063418⟩,
⟨128,444311898,444312147⟩]
theorem checked28916 : checkPrefixCuts (2^48) 3794010113 9 Manual.Count131072.C028916.packed 128 cuts28916 = true := by
 decide +kernel
def pointBounds28916 : List (Nat × Nat × Nat) := [(3794086912,104759500748550,104759883807072)]
theorem point_links_checked28916 : (cuts28916.take 1).map (fun c => (3794010113-1+2*2^9*c.k,104759243685277+c.lower,104759626743654+c.upper)) = pointBounds28916 := by
 decide +kernel
def cuts28917 : List PrefixCut := [⟨63,218107110,218107234⟩,
⟨128,439845490,439845739⟩]
theorem checked28917 : checkPrefixCuts (2^48) 3794141185 9 Manual.Count131072.C028917.packed 128 cuts28917 = true := by
 decide +kernel
def pointBounds28917 : List (Nat × Nat × Nat) := [(3794205696,104759906104285,104760289163035)]
theorem point_links_checked28917 : (cuts28917.take 1).map (fun c => (3794141185-1+2*2^9*c.k,104759687997175+c.lower,104760071055801+c.upper)) = pointBounds28917 := by
 decide +kernel
def cuts28918 : List PrefixCut := [⟨51,180562996,180563096⟩,
⟨128,448954803,448955055⟩]
theorem checked28918 : checkPrefixCuts (2^48) 3794272257 9 Manual.Count131072.C028918.packed 128 cuts28918 = true := by
 decide +kernel
def pointBounds28918 : List (Nat × Nat × Nat) := [(3794324480,104760308405661,104760691464636)]
theorem point_links_checked28918 : (cuts28918.take 1).map (fun c => (3794272257-1+2*2^9*c.k,104760127842665+c.lower,104760510901540+c.upper)) = pointBounds28918 := by
 decide +kernel
def cuts28919 : List PrefixCut := [⟨39,135899972,135900048⟩,
⟨128,441076156,441076405⟩]
theorem checked28919 : checkPrefixCuts (2^48) 3794403329 9 Manual.Count131072.C028919.packed 128 cuts28919 = true := by
 decide +kernel
def pointBounds28919 : List (Nat × Nat × Nat) := [(3794443264,104760712697440,104761095756643)]
theorem point_links_checked28919 : (cuts28919.take 1).map (fun c => (3794403329-1+2*2^9*c.k,104760576797468+c.lower,104760959856595+c.upper)) = pointBounds28919 := by
 decide +kernel
def cuts28920 : List PrefixCut := [⟨27,92204210,92204260⟩,
⟨128,438316361,438316600⟩]
theorem checked28920 : checkPrefixCuts (2^48) 3794534401 9 Manual.Count131072.C028920.packed 128 cuts28920 = true := by
 decide +kernel
def pointBounds28920 : List (Nat × Nat × Nat) := [(3794562048,104761110077834,104761493137260)]
theorem point_links_checked28920 : (cuts28920.take 1).map (fun c => (3794534401-1+2*2^9*c.k,104761017873624+c.lower,104761400933000+c.upper)) = pointBounds28920 := by
 decide +kernel
def cuts28921 : List PrefixCut := [⟨15,53555305,53555337⟩,
⟨128,443864344,443864595⟩]
theorem checked28921 : checkPrefixCuts (2^48) 3794665473 9 Manual.Count131072.C028921.packed 128 cuts28921 = true := by
 decide +kernel
def pointBounds28921 : List (Nat × Nat × Nat) := [(3794680832,104761509745290,104761892804937)]
theorem point_links_checked28921 : (cuts28921.take 1).map (fun c => (3794665473-1+2*2^9*c.k,104761456189985+c.lower,104761839249600+c.upper)) = pointBounds28921 := by
 decide +kernel
def cuts28922 : List PrefixCut := [⟨3,10013473,10013479⟩,
⟨119,404612174,404612400⟩,
⟨128,436505892,436506135⟩]
theorem checked28922 : checkPrefixCuts (2^48) 3794796545 9 Manual.Count131072.C028922.packed 128 cuts28922 = true := by
 decide +kernel
def pointBounds28922 : List (Nat × Nat × Nat) := [(3794799616,104761910067802,104762293127674),(3794918400,104762304666503,104762687726595)]
theorem point_links_checked28922 : (cuts28922.take 2).map (fun c => (3794796545-1+2*2^9*c.k,104761900054329+c.lower,104762283114195+c.upper)) = pointBounds28922 := by
 decide +kernel
def cuts28923 : List PrefixCut := [⟨107,367439568,367439775⟩,
⟨128,438345129,438345377⟩]
theorem checked28923 : checkPrefixCuts (2^48) 3794927617 9 Manual.Count131072.C028923.packed 128 cuts28923 = true := by
 decide +kernel
def pointBounds28923 : List (Nat × Nat × Nat) := [(3795037184,104762703999789,104763087060105)]
theorem point_links_checked28923 : (cuts28923.take 1).map (fun c => (3794927617-1+2*2^9*c.k,104762336560221+c.lower,104762719620330+c.upper)) = pointBounds28923 := by
 decide +kernel
def cuts28924 : List PrefixCut := [⟨95,328786013,328786198⟩,
⟨128,444040834,444041084⟩]
theorem checked28924 : checkPrefixCuts (2^48) 3795058689 9 Manual.Count131072.C028924.packed 128 cuts28924 = true := by
 decide +kernel
def pointBounds28924 : List (Nat × Nat × Nat) := [(3795155968,104763103691363,104763486751905)]
theorem point_links_checked28924 : (cuts28924.take 1).map (fun c => (3795058689-1+2*2^9*c.k,104762774905350+c.lower,104763157965707+c.upper)) = pointBounds28924 := by
 decide +kernel
def cuts28925 : List PrefixCut := [⟨83,280716034,280716195⟩,
⟨128,436238189,436238437⟩]
theorem checked28925 : checkPrefixCuts (2^48) 3795189761 9 Manual.Count131072.C028925.packed 128 cuts28925 = true := by
 decide +kernel
def pointBounds28925 : List (Nat × Nat × Nat) := [(3795274752,104763499662218,104763882722986)]
theorem point_links_checked28925 : (cuts28925.take 1).map (fun c => (3795189761-1+2*2^9*c.k,104763218946184+c.lower,104763602006791+c.upper)) = pointBounds28925 := by
 decide +kernel
def cuts28926 : List PrefixCut := [⟨71,246369340,246369477⟩,
⟨128,438744715,438744958⟩]
theorem checked28926 : checkPrefixCuts (2^48) 3795320833 9 Manual.Count131072.C028926.packed 128 cuts28926 = true := by
 decide +kernel
def pointBounds28926 : List (Nat × Nat × Nat) := [(3795393536,104763901553713,104764284614705)]
theorem point_links_checked28926 : (cuts28926.take 1).map (fun c => (3795320833-1+2*2^9*c.k,104763655184373+c.lower,104764038245228+c.upper)) = pointBounds28926 := by
 decide +kernel
def cuts28927 : List PrefixCut := [⟨59,205202158,205202276⟩,
⟨128,440361066,440361317⟩]
theorem checked28927 : checkPrefixCuts (2^48) 3795451905 9 Manual.Count131072.C028927.packed 128 cuts28927 = true := by
 decide +kernel
def pointBounds28927 : List (Nat × Nat × Nat) := [(3795512320,104764299131246,104764682192462)]
theorem point_links_checked28927 : (cuts28927.take 1).map (fun c => (3795451905-1+2*2^9*c.k,104764093929088+c.lower,104764476990186+c.upper)) = pointBounds28927 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000278
