import PlattAssemblyKernel
import PlattCertificates.Count131072.C014928
import PlattCertificates.Count131072.C014929
import PlattCertificates.Count131072.C014930
import PlattCertificates.Count131072.C014931
import PlattCertificates.Count131072.C014932
import PlattCertificates.Count131072.C014933
import PlattCertificates.Count131072.C014934
import PlattCertificates.Count131072.C014935
import PlattCertificates.Count131072.C014936
import PlattCertificates.Count131072.C014937
import PlattCertificates.Count131072.C014938
import PlattCertificates.Count131072.C014939
import PlattCertificates.Count131072.C014940
import PlattCertificates.Count131072.C014941
import PlattCertificates.Count131072.C014942
import PlattCertificates.Count131072.C014943
import PlattCertificates.Count131072.C014944
import PlattCertificates.Count131072.C014945
import PlattCertificates.Count131072.C014946
import PlattCertificates.Count131072.C014947
import PlattCertificates.Count131072.C014948
import PlattCertificates.Count131072.C014949
import PlattCertificates.Count131072.C014950
import PlattCertificates.Count131072.C014951
import PlattCertificates.Count131072.C014952
import PlattCertificates.Count131072.C014953
import PlattCertificates.Count131072.C014954
import PlattCertificates.Count131072.C014955
import PlattCertificates.Count131072.C014956
import PlattCertificates.Count131072.C014957
import PlattCertificates.Count131072.C014958
import PlattCertificates.Count131072.C014959
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000154
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts14928 : List PrefixCut := [⟨54,367527699,367527945⟩,
⟨114,780409759,780410284⟩,
⟨128,876019673,876020261⟩]
theorem checked14928 : checkPrefixCuts (2^48) 1960574977 9 Manual.Count131072.C014928.packed 128 cuts14928 = true := by
 decide +kernel
def pointBounds14928 : List (Nat × Nat × Nat) := [(1960630272,96205965678526,96206343670580),(1960691712,96206378560586,96206756552919)]
theorem point_links_checked14928 : (cuts14928.take 2).map (fun c => (1960574977-1+2*2^9*c.k,96205598150827+c.lower,96205976142635+c.upper)) = pointBounds14928 := by
 decide +kernel
def cuts14929 : List PrefixCut := [⟨46,313096097,313096306⟩,
⟨106,722076507,722076993⟩,
⟨128,874238607,874239196⟩]
theorem checked14929 : checkPrefixCuts (2^48) 1960706049 9 Manual.Count131072.C014929.packed 128 cuts14929 = true := by
 decide +kernel
def pointBounds14929 : List (Nat × Nat × Nat) := [(1960753152,96206787266597,96207165259202),(1960814592,96207196247007,96207574239889)]
theorem point_links_checked14929 : (cuts14929.take 2).map (fun c => (1960706049-1+2*2^9*c.k,96206474170500+c.lower,96206852162896+c.upper)) = pointBounds14929 := by
 decide +kernel
def cuts14930 : List PrefixCut := [⟨38,261111789,261111963⟩,
⟨98,683128877,683129336⟩,
⟨128,891261644,891262243⟩]
theorem checked14930 : checkPrefixCuts (2^48) 1960837121 9 Manual.Count131072.C014930.packed 128 cuts14930 = true := by
 decide +kernel
def pointBounds14930 : List (Nat × Nat × Nat) := [(1960876032,96207609520896,96207987514055),(1960937472,96208031537984,96208409531428)]
theorem point_links_checked14930 : (cuts14930.take 2).map (fun c => (1960837121-1+2*2^9*c.k,96207348409107+c.lower,96207726402092+c.upper)) = pointBounds14930 := by
 decide +kernel
def cuts14931 : List PrefixCut := [⟨30,199947865,199948001⟩,
⟨90,613039343,613039754⟩,
⟨128,867088419,867088999⟩]
theorem checked14931 : checkPrefixCuts (2^48) 1960968193 9 Manual.Count131072.C014931.packed 128 cuts14931 = true := by
 decide +kernel
def pointBounds14931 : List (Nat × Nat × Nat) := [(1960998912,96208439618616,96208817612336),(1961060352,96208852710094,96209230704089)]
theorem point_links_checked14931 : (cuts14931.take 2).map (fun c => (1960968193-1+2*2^9*c.k,96208239670751+c.lower,96208617664335+c.upper)) = pointBounds14931 := by
 decide +kernel
def cuts14932 : List PrefixCut := [⟨22,152714134,152714238⟩,
⟨82,560612919,560613296⟩,
⟨128,878225478,878226068⟩]
theorem checked14932 : checkPrefixCuts (2^48) 1961099265 9 Manual.Count131072.C014932.packed 128 cuts14932 = true := by
 decide +kernel
def pointBounds14932 : List (Nat × Nat × Nat) := [(1961121792,96209259473304,96209637467572),(1961183232,96209667372089,96210045366630)]
theorem point_links_checked14932 : (cuts14932.take 2).map (fun c => (1961099265-1+2*2^9*c.k,96209106759170+c.lower,96209484753334+c.upper)) = pointBounds14932 := by
 decide +kernel
def cuts14933 : List PrefixCut := [⟨14,95727189,95727253⟩,
⟨74,518813037,518813382⟩,
⟨128,891370172,891370765⟩]
theorem checked14933 : checkPrefixCuts (2^48) 1961230337 9 Manual.Count131072.C014933.packed 128 cuts14933 = true := by
 decide +kernel
def pointBounds14933 : List (Nat × Nat × Nat) := [(1961244672,96210080711837,96210458706655),(1961306112,96210503797685,96210881792784)]
theorem point_links_checked14933 : (cuts14933.take 2).map (fun c => (1961230337-1+2*2^9*c.k,96209984984648+c.lower,96210362979402+c.upper)) = pointBounds14933 := by
 decide +kernel
def cuts14934 : List PrefixCut := [⟨6,40326235,40326263⟩,
⟨66,451904981,451905286⟩,
⟨126,862896917,862897503⟩,
⟨128,879255967,879256563⟩]
theorem checked14934 : checkPrefixCuts (2^48) 1961361409 9 Manual.Count131072.C014934.packed 128 cuts14934 = true := by
 decide +kernel
def pointBounds14934 : List (Nat × Nat × Nat) := [(1961367552,96210916681055,96211294676430),(1961428992,96211328259801,96211706255453),(1961490432,96211739251737,96212117247670)]
theorem point_links_checked14934 : (cuts14934.take 3).map (fun c => (1961361409-1+2*2^9*c.k,96210876354820+c.lower,96211254350167+c.upper)) = pointBounds14934 := by
 decide +kernel
def cuts14935 : List PrefixCut := [⟨58,394046019,394046284⟩,
⟨118,812904338,812904880⟩,
⟨128,883358489,883359078⟩]
theorem checked14935 : checkPrefixCuts (2^48) 1961492481 9 Manual.Count131072.C014935.packed 128 cuts14935 = true := by
 decide +kernel
def pointBounds14935 : List (Nat × Nat × Nat) := [(1961551872,96212149656806,96212527653014),(1961613312,96212568515125,96212946511610)]
theorem point_links_checked14935 : (cuts14935.take 2).map (fun c => (1961492481-1+2*2^9*c.k,96211755610787+c.lower,96212133606730+c.upper)) = pointBounds14935 := by
 decide +kernel
def cuts14936 : List PrefixCut := [⟨50,347960561,347960791⟩,
⟨110,759618310,759618817⟩,
⟨128,883730116,883730706⟩]
theorem checked14936 : checkPrefixCuts (2^48) 1961623553 9 Manual.Count131072.C014936.packed 128 cuts14936 = true := by
 decide +kernel
def pointBounds14936 : List (Nat × Nat × Nat) := [(1961674752,96212986929837,96213364926599),(1961736192,96213398587586,96213776584625)]
theorem point_links_checked14936 : (cuts14936.take 2).map (fun c => (1961623553-1+2*2^9*c.k,96212638969276+c.lower,96213016965808+c.upper)) = pointBounds14936 := by
 decide +kernel
def cuts14937 : List PrefixCut := [⟨42,287246197,287246391⟩,
⟨102,696582645,696583116⟩,
⟨128,873053918,873054506⟩]
theorem checked14937 : checkPrefixCuts (2^48) 1961754625 9 Manual.Count131072.C014937.packed 128 cuts14937 = true := by
 decide +kernel
def pointBounds14937 : List (Nat × Nat × Nat) := [(1961797632,96213809945589,96214187942905),(1961859072,96214219282037,96214597279630)]
theorem point_links_checked14937 : (cuts14937.take 2).map (fun c => (1961754625-1+2*2^9*c.k,96213522699392+c.lower,96213900696514+c.upper)) = pointBounds14937 := by
 decide +kernel
def cuts14938 : List PrefixCut := [⟨34,240312763,240312924⟩,
⟨94,656940439,656940879⟩,
⟨128,890068253,890068844⟩]
theorem checked14938 : checkPrefixCuts (2^48) 1961885697 9 Manual.Count131072.C014938.packed 128 cuts14938 = true := by
 decide +kernel
def pointBounds14938 : List (Nat × Nat × Nat) := [(1961920512,96214636066073,96215014063944),(1961981952,96215052693749,96215430691899)]
theorem point_links_checked14938 : (cuts14938.take 2).map (fun c => (1961885697-1+2*2^9*c.k,96214395753310+c.lower,96214773751020+c.upper)) = pointBounds14938 := by
 decide +kernel
def cuts14939 : List PrefixCut := [⟨26,180904369,180904487⟩,
⟨86,581151713,581152102⟩,
⟨128,880253312,880253902⟩]
theorem checked14939 : checkPrefixCuts (2^48) 1962016769 9 Manual.Count131072.C014939.packed 128 cuts14939 = true := by
 decide +kernel
def pointBounds14939 : List (Nat × Nat × Nat) := [(1962043392,96215466725932,96215844724351),(1962104832,96215866973276,96216244971966)]
theorem point_links_checked14939 : (cuts14939.take 2).map (fun c => (1962016769-1+2*2^9*c.k,96215285821563+c.lower,96215663819864+c.upper)) = pointBounds14939 := by
 decide +kernel
def cuts14940 : List PrefixCut := [⟨18,125376832,125376917⟩,
⟨78,527463947,527464304⟩,
⟨128,873596116,873596701⟩]
theorem checked14940 : checkPrefixCuts (2^48) 1962147841 9 Manual.Count131072.C014940.packed 128 cuts14940 = true := by
 decide +kernel
def pointBounds14940 : List (Nat × Nat × Nat) := [(1962166272,96216291451707,96216669450683),(1962227712,96216693538822,96217071538070)]
theorem point_links_checked14940 : (cuts14940.take 2).map (fun c => (1962147841-1+2*2^9*c.k,96216166074875+c.lower,96216544073766+c.upper)) = pointBounds14940 := by
 decide +kernel
def cuts14941 : List PrefixCut := [⟨10,69856482,69856526⟩,
⟨70,489991813,489992138⟩,
⟨128,884152391,884152980⟩]
theorem checked14941 : checkPrefixCuts (2^48) 1962278913 9 Manual.Count131072.C014941.packed 128 cuts14941 = true := by
 decide +kernel
def pointBounds14941 : List (Nat × Nat × Nat) := [(1962289152,96217109527473,96217487526993),(1962350592,96217529662804,96217907662605)]
theorem point_links_checked14941 : (cuts14941.take 2).map (fun c => (1962278913-1+2*2^9*c.k,96217039670991+c.lower,96217417670467+c.upper)) = pointBounds14941 := by
 decide +kernel
def cuts14942 : List PrefixCut := [⟨2,13769587,13769595⟩,
⟨62,410069130,410069401⟩,
⟨122,816252668,816253208⟩,
⟨128,854546854,854547419⟩]
theorem checked14942 : checkPrefixCuts (2^48) 1962409985 9 Manual.Count131072.C014942.packed 128 cuts14942 = true := by
 decide +kernel
def pointBounds14942 : List (Nat × Nat × Nat) := [(1962412032,96217937592969,96218315593042),(1962473472,96218333892512,96218711892848),(1962534912,96218740076050,96219118076655)]
theorem point_links_checked14942 : (cuts14942.take 3).map (fun c => (1962409985-1+2*2^9*c.k,96217923823382+c.lower,96218301823447+c.upper)) = pointBounds14942 := by
 decide +kernel
def cuts14943 : List PrefixCut := [⟨54,370171299,370171545⟩,
⟨114,775612297,775612813⟩,
⟨128,876432788,876433370⟩]
theorem checked14943 : checkPrefixCuts (2^48) 1962541057 9 Manual.Count131072.C014943.packed 128 cuts14943 = true := by
 decide +kernel
def pointBounds14943 : List (Nat × Nat × Nat) := [(1962596352,96219148541535,96219526542411),(1962657792,96219553982533,96219931983679)]
theorem point_links_checked14943 : (cuts14943.take 2).map (fun c => (1962541057-1+2*2^9*c.k,96218778370236+c.lower,96219156370866+c.upper)) = pointBounds14943 := by
 decide +kernel
def cuts14944 : List PrefixCut := [⟨46,311778494,311778698⟩,
⟨106,727806295,727806777⟩,
⟨128,877091277,877091859⟩]
theorem checked14944 : checkPrefixCuts (2^48) 1962672129 9 Manual.Count131072.C014944.packed 128 cuts14944 = true := by
 decide +kernel
def pointBounds14944 : List (Nat × Nat × Nat) := [(1962719232,96219966581518,96220344582934),(1962780672,96220382609319,96220760611013)]
theorem point_links_checked14944 : (cuts14944.take 2).map (fun c => (1962672129-1+2*2^9*c.k,96219654803024+c.lower,96220032804236+c.upper)) = pointBounds14944 := by
 decide +kernel
def cuts14945 : List PrefixCut := [⟨38,262427709,262427883⟩,
⟨98,676421979,676422431⟩,
⟨128,879470823,879471408⟩]
theorem checked14945 : checkPrefixCuts (2^48) 1962803201 9 Manual.Count131072.C014945.packed 128 cuts14945 = true := by
 decide +kernel
def pointBounds14945 : List (Nat × Nat × Nat) := [(1962842112,96220794322010,96221172323978),(1962903552,96221208316280,96221586318526)]
theorem point_links_checked14945 : (cuts14945.take 2).map (fun c => (1962803201-1+2*2^9*c.k,96220531894301+c.lower,96220909896095+c.upper)) = pointBounds14945 := by
 decide +kernel
def cuts14946 : List PrefixCut := [⟨30,198887248,198887385⟩,
⟨90,613859351,613859769⟩,
⟨128,878121228,878121816⟩]
theorem checked14946 : checkPrefixCuts (2^48) 1962934273 9 Manual.Count131072.C014946.packed 128 cuts14946 = true := by
 decide +kernel
def pointBounds14946 : List (Nat × Nat × Nat) := [(1962964992,96221610252372,96221988254888),(1963026432,96222025224475,96222403227272)]
theorem point_links_checked14946 : (cuts14946.take 2).map (fun c => (1962934273-1+2*2^9*c.k,96221411365124+c.lower,96221789367503+c.upper)) = pointBounds14946 := by
 decide +kernel
def cuts14947 : List PrefixCut := [⟨22,149980247,149980350⟩,
⟨82,561341800,561342179⟩,
⟨128,877345893,877346481⟩]
theorem checked14947 : checkPrefixCuts (2^48) 1963065345 9 Manual.Count131072.C014947.packed 128 cuts14947 = true := by
 decide +kernel
def pointBounds14947 : List (Nat × Nat × Nat) := [(1963087872,96222439466599,96222817469669),(1963149312,96222850828152,96223228831498)]
theorem point_links_checked14947 : (cuts14947.take 2).map (fun c => (1963065345-1+2*2^9*c.k,96222289486352+c.lower,96222667489319+c.upper)) = pointBounds14947 := by
 decide +kernel
def cuts14948 : List PrefixCut := [⟨14,96204812,96204877⟩,
⟨74,513418875,513419212⟩,
⟨128,883595679,883596259⟩]
theorem checked14948 : checkPrefixCuts (2^48) 1963196417 9 Manual.Count131072.C014948.packed 128 cuts14948 = true := by
 decide +kernel
def pointBounds14948 : List (Nat × Nat × Nat) := [(1963210752,96223263037057,96223641040677),(1963272192,96223680251120,96224058255012)]
theorem point_links_checked14948 : (cuts14948.take 2).map (fun c => (1963196417-1+2*2^9*c.k,96223166832245+c.lower,96223544835800+c.upper)) = pointBounds14948 := by
 decide +kernel
def cuts14949 : List PrefixCut := [⟨6,40429216,40429245⟩,
⟨66,450018930,450019234⟩,
⟨126,863753144,863753728⟩,
⟨128,877372035,877372628⟩]
theorem checked14949 : checkPrefixCuts (2^48) 1963327489 9 Manual.Count131072.C014949.packed 128 cuts14949 = true := by
 decide +kernel
def pointBounds14949 : List (Nat × Nat × Nat) := [(1963333632,96224090857140,96224468861304),(1963395072,96224500446854,96224878451293),(1963456512,96224914181068,96225292185787)]
theorem point_links_checked14949 : (cuts14949.take 3).map (fun c => (1963327489-1+2*2^9*c.k,96224050427924+c.lower,96224428432059+c.upper)) = pointBounds14949 := by
 decide +kernel
def cuts14950 : List PrefixCut := [⟨58,402539524,402539789⟩,
⟨118,808650354,808650897⟩,
⟨128,877170445,877171035⟩]
theorem checked14950 : checkPrefixCuts (2^48) 1963458561 9 Manual.Count131072.C014950.packed 128 cuts14950 = true := by
 decide +kernel
def pointBounds14950 : List (Nat × Nat × Nat) := [(1963517952,96225330339483,96225708344476),(1963579392,96225736450313,96226114455584)]
theorem point_links_checked14950 : (cuts14950.take 2).map (fun c => (1963458561-1+2*2^9*c.k,96224927799959+c.lower,96225305804687+c.upper)) = pointBounds14950 := by
 decide +kernel
def cuts14951 : List PrefixCut := [⟨50,352342682,352342913⟩,
⟨110,765738467,765738968⟩,
⟨128,889152677,889153260⟩]
theorem checked14951 : checkPrefixCuts (2^48) 1963589633 9 Manual.Count131072.C014951.packed 128 cuts14951 = true := by
 decide +kernel
def pointBounds14951 : List (Nat × Nat × Nat) := [(1963640832,96226157313086,96226535318635),(1963702272,96226570708871,96226948714690)]
theorem point_links_checked14951 : (cuts14951.take 2).map (fun c => (1963589633-1+2*2^9*c.k,96225804970404+c.lower,96226182975722+c.upper)) = pointBounds14951 := by
 decide +kernel
def cuts14952 : List PrefixCut := [⟨42,284521903,284522091⟩,
⟨102,697031799,697032260⟩,
⟨128,869743182,869743757⟩]
theorem checked14952 : checkPrefixCuts (2^48) 1963720705 9 Manual.Count131072.C014952.packed 128 cuts14952 = true := by
 decide +kernel
def pointBounds14952 : List (Nat × Nat × Nat) := [(1963763712,96226978644984,96227356651073),(1963825152,96227391154880,96227769161242)]
theorem point_links_checked14952 : (cuts14952.take 2).map (fun c => (1963720705-1+2*2^9*c.k,96226694123081+c.lower,96227072128982+c.upper)) = pointBounds14952 := by
 decide +kernel
def cuts14953 : List PrefixCut := [⟨34,235485763,235485918⟩,
⟨94,656712710,656713141⟩,
⟨128,895913225,895913820⟩]
theorem checked14953 : checkPrefixCuts (2^48) 1963851777 9 Manual.Count131072.C014953.packed 128 cuts14953 = true := by
 decide +kernel
def pointBounds14953 : List (Nat × Nat × Nat) := [(1963886592,96227799352026,96228177358657),(1963948032,96228220578973,96228598585880)]
theorem point_links_checked14953 : (cuts14953.take 2).map (fun c => (1963851777-1+2*2^9*c.k,96227563866263+c.lower,96227941872739+c.upper)) = pointBounds14953 := by
 decide +kernel
def cuts14954 : List PrefixCut := [⟨26,173700739,173700857⟩,
⟨86,582432986,582433374⟩,
⟨128,857732274,857732850⟩]
theorem checked14954 : checkPrefixCuts (2^48) 1963982849 9 Manual.Count131072.C014954.packed 128 cuts14954 = true := by
 decide +kernel
def pointBounds14954 : List (Nat × Nat × Nat) := [(1964009472,96228633480227,96229011487416),(1964070912,96229042212474,96229420219933)]
theorem point_links_checked14954 : (cuts14954.take 2).map (fun c => (1963982849-1+2*2^9*c.k,96228459779488+c.lower,96228837786559+c.upper)) = pointBounds14954 := by
 decide +kernel
def cuts14955 : List PrefixCut := [⟨18,120808781,120808863⟩,
⟨78,530088533,530088894⟩,
⟨128,870285421,870286013⟩]
theorem checked14955 : checkPrefixCuts (2^48) 1964113921 9 Manual.Count131072.C014955.packed 128 cuts14955 = true := by
 decide +kernel
def pointBounds14955 : List (Nat × Nat × Nat) := [(1964132352,96229438320543,96229816328272),(1964193792,96229847600295,96230225608303)]
theorem point_links_checked14955 : (cuts14955.take 2).map (fun c => (1964113921-1+2*2^9*c.k,96229317511762+c.lower,96229695519409+c.upper)) = pointBounds14955 := by
 decide +kernel
def cuts14956 : List PrefixCut := [⟨10,67637083,67637129⟩,
⟨70,484056076,484056405⟩,
⟨128,889428833,889429431⟩]
theorem checked14956 : checkPrefixCuts (2^48) 1964244993 9 Manual.Count131072.C014956.packed 128 cuts14956 = true := by
 decide +kernel
def pointBounds14956 : List (Nat × Nat × Nat) := [(1964255232,96230255434266,96230633442551),(1964316672,96230671853259,96231049861827)]
theorem point_links_checked14956 : (cuts14956.take 2).map (fun c => (1964244993-1+2*2^9*c.k,96230187797183+c.lower,96230565805422+c.upper)) = pointBounds14956 := by
 decide +kernel
def cuts14957 : List PrefixCut := [⟨2,13182646,13182656⟩,
⟨62,421264949,421265232⟩,
⟨122,833632917,833633476⟩,
⟨128,875614068,875614655⟩]
theorem checked14957 : checkPrefixCuts (2^48) 1964376065 9 Manual.Count131072.C014957.packed 128 cuts14957 = true := by
 decide +kernel
def pointBounds14957 : List (Nat × Nat × Nat) := [(1964378112,96231090408662,96231468417509),(1964439552,96231498490965,96231876500085),(1964500992,96231910858933,96232288868329)]
theorem point_links_checked14957 : (cuts14957.take 3).map (fun c => (1964376065-1+2*2^9*c.k,96231077226016+c.lower,96231455234853+c.upper)) = pointBounds14957 := by
 decide +kernel
def cuts14958 : List PrefixCut := [⟨54,367508474,367508718⟩,
⟨114,774836094,774836609⟩,
⟨128,869968114,869968695⟩]
theorem checked14958 : checkPrefixCuts (2^48) 1964507137 9 Manual.Count131072.C014958.packed 128 cuts14958 = true := by
 decide +kernel
def pointBounds14958 : List (Nat × Nat × Nat) := [(1964562432,96232320348558,96232698358226),(1964623872,96232727676178,96233105686117)]
theorem point_links_checked14958 : (cuts14958.take 2).map (fun c => (1964507137-1+2*2^9*c.k,96231952840084+c.lower,96232330849508+c.upper)) = pointBounds14958 := by
 decide +kernel
def cuts14959 : List PrefixCut := [⟨46,321638703,321638917⟩,
⟨106,732092685,732093175⟩,
⟨128,880511980,880512570⟩]
theorem checked14959 : checkPrefixCuts (2^48) 1964638209 9 Manual.Count131072.C014959.packed 128 cuts14959 = true := by
 decide +kernel
def pointBounds14959 : List (Nat × Nat × Nat) := [(1964685312,96233144446901,96233522457120),(1964746752,96233554900883,96233932911378)]
theorem point_links_checked14959 : (cuts14959.take 2).map (fun c => (1964638209-1+2*2^9*c.k,96232822808198+c.lower,96233200818203+c.upper)) = pointBounds14959 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000154
