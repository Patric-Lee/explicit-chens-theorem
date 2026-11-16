import PlattAssemblyKernel
import PlattCertificates.Count131072.C011888
import PlattCertificates.Count131072.C011889
import PlattCertificates.Count131072.C011890
import PlattCertificates.Count131072.C011891
import PlattCertificates.Count131072.C011892
import PlattCertificates.Count131072.C011893
import PlattCertificates.Count131072.C011894
import PlattCertificates.Count131072.C011895
import PlattCertificates.Count131072.C011896
import PlattCertificates.Count131072.C011897
import PlattCertificates.Count131072.C011898
import PlattCertificates.Count131072.C011899
import PlattCertificates.Count131072.C011900
import PlattCertificates.Count131072.C011901
import PlattCertificates.Count131072.C011902
import PlattCertificates.Count131072.C011903
import PlattCertificates.Count131072.C011904
import PlattCertificates.Count131072.C011905
import PlattCertificates.Count131072.C011906
import PlattCertificates.Count131072.C011907
import PlattCertificates.Count131072.C011908
import PlattCertificates.Count131072.C011909
import PlattCertificates.Count131072.C011910
import PlattCertificates.Count131072.C011911
import PlattCertificates.Count131072.C011912
import PlattCertificates.Count131072.C011913
import PlattCertificates.Count131072.C011914
import PlattCertificates.Count131072.C011915
import PlattCertificates.Count131072.C011916
import PlattCertificates.Count131072.C011917
import PlattCertificates.Count131072.C011918
import PlattCertificates.Count131072.C011919
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000059
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts11888 : List PrefixCut := [⟨25,221629599,221629770⟩,
⟨73,636769809,636770298⟩,
⟨121,1049374497,1049375306⟩,
⟨128,1105588621,1105589472⟩]
theorem checked11888 : checkPrefixCuts (2^48) 1562116097 9 Manual.Count131072.C011888.packed 128 cuts11888 = true := by
 decide +kernel
def pointBounds11888 : List (Nat × Nat × Nat) := [(1562141696,93201195830911,93201571671519),(1562190848,93201610971121,93201986812047),(1562240000,93202023575809,93202399417055)]
theorem point_links_checked11888 : (cuts11888.take 3).map (fun c => (1562116097-1+2*2^9*c.k,93200974201312+c.lower,93201350041749+c.upper)) = pointBounds11888 := by
 decide +kernel
def cuts11889 : List PrefixCut := [⟨41,363764599,363764880⟩,
⟨89,781568192,781568791⟩,
⟨128,1118467844,1118468707⟩]
theorem checked11889 : checkPrefixCuts (2^48) 1562247169 9 Manual.Count131072.C011889.packed 128 cuts11889 = true := by
 decide +kernel
def pointBounds11889 : List (Nat × Nat × Nat) := [(1562289152,93202443554532,93202819396101),(1562338304,93202861358125,93203237200012)]
theorem point_links_checked11889 : (cuts11889.take 2).map (fun c => (1562247169-1+2*2^9*c.k,93202079789933+c.lower,93202455631221+c.upper)) = pointBounds11889 := by
 decide +kernel
def cuts11890 : List PrefixCut := [⟨9,77287541,77287599⟩,
⟨57,502991597,502991978⟩,
⟨105,927601438,927602145⟩,
⟨128,1127021062,1127021920⟩]
theorem checked11890 : checkPrefixCuts (2^48) 1562378241 9 Manual.Count131072.C011890.packed 128 cuts11890 = true := by
 decide +kernel
def pointBounds11890 : List (Nat × Nat × Nat) := [(1562387456,93203275545318,93203651387527),(1562436608,93203701249374,93204077091906),(1562485760,93204125859215,93204501702073)]
theorem point_links_checked11890 : (cuts11890.take 3).map (fun c => (1562378241-1+2*2^9*c.k,93203198257777+c.lower,93203574099928+c.upper)) = pointBounds11890 := by
 decide +kernel
def cuts11891 : List PrefixCut := [⟨25,214548357,214548519⟩,
⟨73,628503313,628503794⟩,
⟨121,1050010796,1050011601⟩,
⟨128,1108552445,1108553294⟩]
theorem checked11891 : checkPrefixCuts (2^48) 1562509313 9 Manual.Count131072.C011891.packed 128 cuts11891 = true := by
 decide +kernel
def pointBounds11891 : List (Nat × Nat × Nat) := [(1562534912,93204539827196,93204915670367),(1562584064,93204953782152,93205329625642),(1562633216,93205375289635,93205751133449)]
theorem point_links_checked11891 : (cuts11891.take 3).map (fun c => (1562509313-1+2*2^9*c.k,93204325278839+c.lower,93204701121848+c.upper)) = pointBounds11891 := by
 decide +kernel
def cuts11892 : List PrefixCut := [⟨41,355927618,355927894⟩,
⟨89,767682076,767682672⟩,
⟨128,1105037296,1105038151⟩]
theorem checked11892 : checkPrefixCuts (2^48) 1562640385 9 Manual.Count131072.C011892.packed 128 cuts11892 = true := by
 decide +kernel
def pointBounds11892 : List (Nat × Nat × Nat) := [(1562682368,93205789758902,93206165603036),(1562731520,93206201513360,93206577357814)]
theorem point_links_checked11892 : (cuts11892.take 2).map (fun c => (1562640385-1+2*2^9*c.k,93205433831284+c.lower,93205809675142+c.upper)) = pointBounds11892 := by
 decide +kernel
def cuts11893 : List PrefixCut := [⟨9,76187421,76187480⟩,
⟨57,499983234,499983615⟩,
⟨105,919083024,919083727⟩,
⟨128,1120973853,1120974711⟩]
theorem checked11893 : checkPrefixCuts (2^48) 1562771457 9 Manual.Count131072.C011893.packed 128 cuts11893 = true := by
 decide +kernel
def pointBounds11893 : List (Nat × Nat × Nat) := [(1562780672,93206615056001,93206990900773),(1562829824,93207038851814,93207414696908),(1562878976,93207457951604,93207833797020)]
theorem point_links_checked11893 : (cuts11893.take 3).map (fun c => (1562771457-1+2*2^9*c.k,93206538868580+c.lower,93206914713293+c.upper)) = pointBounds11893 := by
 decide +kernel
def cuts11894 : List PrefixCut := [⟨25,213954090,213954254⟩,
⟨73,625643644,625644131⟩,
⟨121,1046684853,1046685669⟩,
⟨128,1104491442,1104492303⟩]
theorem checked11894 : checkPrefixCuts (2^48) 1562902529 9 Manual.Count131072.C011894.packed 128 cuts11894 = true := by
 decide +kernel
def pointBounds11894 : List (Nat × Nat × Nat) := [(1562928128,93207873796523,93208249642258),(1562977280,93208285486077,93208661332135),(1563026432,93208706527286,93209082373673)]
theorem point_links_checked11894 : (cuts11894.take 3).map (fun c => (1562902529-1+2*2^9*c.k,93207659842433+c.lower,93208035688004+c.upper)) = pointBounds11894 := by
 decide +kernel
def cuts11895 : List PrefixCut := [⟨41,353136880,353137154⟩,
⟨89,769289624,769290218⟩,
⟨128,1107640466,1107641324⟩]
theorem checked11895 : checkPrefixCuts (2^48) 1563033601 9 Manual.Count131072.C011895.packed 128 cuts11895 = true := by
 decide +kernel
def pointBounds11895 : List (Nat × Nat × Nat) := [(1563075584,93209117470755,93209493317461),(1563124736,93209533623499,93209909470525)]
theorem point_links_checked11895 : (cuts11895.take 2).map (fun c => (1563033601-1+2*2^9*c.k,93208764333875+c.lower,93209140180307+c.upper)) = pointBounds11895 := by
 decide +kernel
def cuts11896 : List PrefixCut := [⟨9,78148989,78149050⟩,
⟨57,491754620,491754994⟩,
⟨105,902646391,902647081⟩,
⟨128,1102865944,1102866786⟩]
theorem checked11896 : checkPrefixCuts (2^48) 1563164673 9 Manual.Count131072.C011896.packed 128 cuts11896 = true := by
 decide +kernel
def pointBounds11896 : List (Nat × Nat × Nat) := [(1563173888,93209950123330,93210325970681),(1563223040,93210363728961,93210739576625),(1563272192,93210774620732,93211150468712)]
theorem point_links_checked11896 : (cuts11896.take 3).map (fun c => (1563164673-1+2*2^9*c.k,93209871974341+c.lower,93210247821631+c.upper)) = pointBounds11896 := by
 decide +kernel
def cuts11897 : List PrefixCut := [⟨25,215880832,215880996⟩,
⟨73,637909617,637910110⟩,
⟨121,1060645354,1060646176⟩,
⟨128,1119337585,1119338453⟩]
theorem checked11897 : checkPrefixCuts (2^48) 1563295745 9 Manual.Count131072.C011897.packed 128 cuts11897 = true := by
 decide +kernel
def pointBounds11897 : List (Nat × Nat × Nat) := [(1563321344,93211190721117,93211566569413),(1563370496,93211612749902,93211988598527),(1563419648,93212035485639,93212411334593)]
theorem point_links_checked11897 : (cuts11897.take 3).map (fun c => (1563295745-1+2*2^9*c.k,93210974840285+c.lower,93211350688417+c.upper)) = pointBounds11897 := by
 decide +kernel
def cuts11898 : List PrefixCut := [⟨41,361329712,361329990⟩,
⟨89,783858979,783859581⟩,
⟨128,1130585879,1130586748⟩]
theorem checked11898 : checkPrefixCuts (2^48) 1563426817 9 Manual.Count131072.C011898.packed 128 cuts11898 = true := by
 decide +kernel
def pointBounds11898 : List (Nat × Nat × Nat) := [(1563468800,93212455507582,93212831356860),(1563517952,93212878036849,93213253886451)]
theorem point_links_checked11898 : (cuts11898.take 2).map (fun c => (1563426817-1+2*2^9*c.k,93212094177870+c.lower,93212470026870+c.upper)) = pointBounds11898 := by
 decide +kernel
def cuts11899 : List PrefixCut := [⟨9,77409245,77409305⟩,
⟨57,496311470,496311855⟩,
⟨105,918980793,918981506⟩,
⟨128,1118069968,1118070834⟩]
theorem checked11899 : checkPrefixCuts (2^48) 1563557889 9 Manual.Count131072.C011899.packed 128 cuts11899 = true := by
 decide +kernel
def pointBounds11899 : List (Nat × Nat × Nat) := [(1563567104,93213302172994,93213678022923),(1563616256,93213721075219,93214096925473),(1563665408,93214143744542,93214519595124)]
theorem point_links_checked11899 : (cuts11899.take 3).map (fun c => (1563557889-1+2*2^9*c.k,93213224763749+c.lower,93213600613618+c.upper)) = pointBounds11899 := by
 decide +kernel
def cuts11900 : List PrefixCut := [⟨25,217086570,217086740⟩,
⟨73,635949372,635949869⟩,
⟨121,1056778810,1056779632⟩,
⟨128,1115996272,1115997138⟩]
theorem checked11900 : checkPrefixCuts (2^48) 1563688961 9 Manual.Count131072.C011900.packed 128 cuts11900 = true := by
 decide +kernel
def pointBounds11900 : List (Nat × Nat × Nat) := [(1563714560,93214559920287,93214935771192),(1563763712,93214978783089,93215354634321),(1563812864,93215399612527,93215775464084)]
theorem point_links_checked11900 : (cuts11900.take 3).map (fun c => (1563688961-1+2*2^9*c.k,93214342833717+c.lower,93214718684452+c.upper)) = pointBounds11900 := by
 decide +kernel
def cuts11901 : List PrefixCut := [⟨41,369698298,369698580⟩,
⟨89,775202691,775203286⟩,
⟨128,1117162912,1117163770⟩]
theorem checked11901 : checkPrefixCuts (2^48) 1563820033 9 Manual.Count131072.C011901.packed 128 cuts11901 = true := by
 decide +kernel
def pointBounds11901 : List (Nat × Nat × Nat) := [(1563862016,93215828528287,93216204380170),(1563911168,93216234032680,93216609884876)]
theorem point_links_checked11901 : (cuts11901.take 2).map (fun c => (1563820033-1+2*2^9*c.k,93215458829989+c.lower,93215834681590+c.upper)) = pointBounds11901 := by
 decide +kernel
def cuts11902 : List PrefixCut := [⟨9,77389783,77389843⟩,
⟨57,500505998,500506384⟩,
⟨105,914070780,914071488⟩,
⟨128,1115629385,1115630248⟩]
theorem checked11902 : checkPrefixCuts (2^48) 1563951105 9 Manual.Count131072.C011902.packed 128 cuts11902 = true := by
 decide +kernel
def pointBounds11902 : List (Nat × Nat × Nat) := [(1563960320,93216653382684,93217029235203),(1564009472,93217076498899,93217452351744),(1564058624,93217490063681,93217865916848)]
theorem point_links_checked11902 : (cuts11902.take 3).map (fun c => (1563951105-1+2*2^9*c.k,93216575992901+c.lower,93216951845360+c.upper)) = pointBounds11902 := by
 decide +kernel
def cuts11903 : List PrefixCut := [⟨25,215772308,215772475⟩,
⟨73,623552416,623552895⟩,
⟨121,1042836485,1042837288⟩,
⟨128,1100239585,1100240432⟩]
theorem checked11903 : checkPrefixCuts (2^48) 1564082177 9 Manual.Count131072.C011903.packed 128 cuts11903 = true := by
 decide +kernel
def pointBounds11903 : List (Nat × Nat × Nat) := [(1564107776,93217907394594,93218283248083),(1564156928,93218315174702,93218691028503),(1564206080,93218734458771,93219110312896)]
theorem point_links_checked11903 : (cuts11903.take 3).map (fun c => (1564082177-1+2*2^9*c.k,93217691622286+c.lower,93218067475608+c.upper)) = pointBounds11903 := by
 decide +kernel
def cuts11904 : List PrefixCut := [⟨41,359888478,359888757⟩,
⟨89,781125496,781126097⟩,
⟨128,1127678119,1127678988⟩]
theorem checked11904 : checkPrefixCuts (2^48) 1564213249 9 Manual.Count131072.C011904.packed 128 cuts11904 = true := by
 decide +kernel
def pointBounds11904 : List (Nat × Nat × Nat) := [(1564255232,93219151750349,93219527604797),(1564304384,93219572987367,93219948842137)]
theorem point_links_checked11904 : (cuts11904.take 2).map (fun c => (1564213249-1+2*2^9*c.k,93218791861871+c.lower,93219167716040+c.upper)) = pointBounds11904 := by
 decide +kernel
def cuts11905 : List PrefixCut := [⟨9,79709434,79709496⟩,
⟨57,488684939,488685317⟩,
⟨105,905384198,905384897⟩,
⟨128,1108871210,1108872064⟩]
theorem checked11905 : checkPrefixCuts (2^48) 1564344321 9 Manual.Count131072.C011905.packed 128 cuts11905 = true := by
 decide +kernel
def pointBounds11905 : List (Nat × Nat × Nat) := [(1564353536,93219999249424,93220375104524),(1564402688,93220408224929,93220784080345),(1564451840,93220824924188,93221200779925)]
theorem point_links_checked11905 : (cuts11905.take 3).map (fun c => (1564344321-1+2*2^9*c.k,93219919539990+c.lower,93220295395028+c.upper)) = pointBounds11905 := by
 decide +kernel
def cuts11906 : List PrefixCut := [⟨25,208161657,208161820⟩,
⟨73,636349123,636349613⟩,
⟨121,1045093440,1045094245⟩,
⟨128,1105180643,1105181493⟩]
theorem checked11906 : checkPrefixCuts (2^48) 1564475393 9 Manual.Count131072.C011906.packed 128 cuts11906 = true := by
 decide +kernel
def pointBounds11906 : List (Nat × Nat × Nat) := [(1564500992,93221236572857,93221612428912),(1564550144,93221664760323,93222040616705),(1564599296,93222073504640,93222449361337)]
theorem point_links_checked11906 : (cuts11906.take 3).map (fun c => (1564475393-1+2*2^9*c.k,93221028411200+c.lower,93221404267092+c.upper)) = pointBounds11906 := by
 decide +kernel
def cuts11907 : List PrefixCut := [⟨41,348284444,348284708⟩,
⟨89,763659099,763659683⟩,
⟨128,1095373696,1095374536⟩]
theorem checked11907 : checkPrefixCuts (2^48) 1564606465 9 Manual.Count131072.C011907.packed 128 cuts11907 = true := by
 decide +kernel
def pointBounds11907 : List (Nat × Nat × Nat) := [(1564648448,93222481876287,93222857733293),(1564697600,93222897250942,93223273108268)]
theorem point_links_checked11907 : (cuts11907.take 2).map (fun c => (1564606465-1+2*2^9*c.k,93222133591843+c.lower,93222509448585+c.upper)) = pointBounds11907 := by
 decide +kernel
def cuts11908 : List PrefixCut := [⟨9,76091689,76091748⟩,
⟨57,490181051,490181431⟩,
⟨105,912172069,912172773⟩,
⟨128,1109672179,1109673034⟩]
theorem checked11908 : checkPrefixCuts (2^48) 1564737537 9 Manual.Count131072.C011908.packed 128 cuts11908 = true := by
 decide +kernel
def pointBounds11908 : List (Nat × Nat × Nat) := [(1564746752,93223305057228,93223680914869),(1564795904,93223719146590,93224095004552),(1564845056,93224141137608,93224516995894)]
theorem point_links_checked11908 : (cuts11908.take 3).map (fun c => (1564737537-1+2*2^9*c.k,93223228965539+c.lower,93223604823121+c.upper)) = pointBounds11908 := by
 decide +kernel
def cuts11909 : List PrefixCut := [⟨25,216383340,216383507⟩,
⟨73,634750460,634750949⟩,
⟨121,1049687057,1049687869⟩,
⟨128,1107780739,1107781597⟩]
theorem checked11909 : checkPrefixCuts (2^48) 1564868609 9 Manual.Count131072.C011909.packed 128 cuts11909 = true := by
 decide +kernel
def pointBounds11909 : List (Nat × Nat × Nat) := [(1564894208,93224555021058,93224930879662),(1564943360,93224973388178,93225349247104),(1564992512,93225388324775,93225764184024)]
theorem point_links_checked11909 : (cuts11909.take 3).map (fun c => (1564868609-1+2*2^9*c.k,93224338637718+c.lower,93224714496155+c.upper)) = pointBounds11909 := by
 decide +kernel
def cuts11910 : List PrefixCut := [⟨41,355211188,355211459⟩,
⟨89,780552997,780553592⟩,
⟨128,1110385789,1110386643⟩]
theorem checked11910 : checkPrefixCuts (2^48) 1564999681 9 Manual.Count131072.C011910.packed 128 cuts11910 = true := by
 decide +kernel
def pointBounds11910 : List (Nat × Nat × Nat) := [(1565041664,93225801629645,93226177489211),(1565090816,93226226971454,93226602831344)]
theorem point_links_checked11910 : (cuts11910.take 2).map (fun c => (1564999681-1+2*2^9*c.k,93225446418457+c.lower,93225822277752+c.upper)) = pointBounds11910 := by
 decide +kernel
def cuts11911 : List PrefixCut := [⟨9,78230660,78230721⟩,
⟨57,490777348,490777726⟩,
⟨105,915539545,915540248⟩,
⟨128,1118205065,1118205925⟩]
theorem checked11911 : checkPrefixCuts (2^48) 1565130753 9 Manual.Count131072.C011911.packed 128 cuts11911 = true := by
 decide +kernel
def pointBounds11911 : List (Nat × Nat × Nat) := [(1565139968,93226635034906,93227010895116),(1565189120,93227047581594,93227423442121),(1565238272,93227472343791,93227848204643)]
theorem point_links_checked11911 : (cuts11911.take 3).map (fun c => (1565130753-1+2*2^9*c.k,93226556804246+c.lower,93226932664395+c.upper)) = pointBounds11911 := by
 decide +kernel
def cuts11912 : List PrefixCut := [⟨25,216688601,216688768⟩,
⟨73,635490083,635490571⟩,
⟨121,1061291305,1061292118⟩,
⟨128,1123326244,1123327106⟩]
theorem checked11912 : checkPrefixCuts (2^48) 1565261825 9 Manual.Count131072.C011912.packed 128 cuts11912 = true := by
 decide +kernel
def pointBounds11912 : List (Nat × Nat × Nat) := [(1565287424,93227891697912,93228267559088),(1565336576,93228310499394,93228686360891),(1565385728,93228736300616,93229112162438)]
theorem point_links_checked11912 : (cuts11912.take 3).map (fun c => (1565261825-1+2*2^9*c.k,93227675009311+c.lower,93228050870320+c.upper)) = pointBounds11912 := by
 decide +kernel
def cuts11913 : List PrefixCut := [⟨41,356920042,356920318⟩,
⟨89,768310145,768310736⟩,
⟨128,1105072245,1105073093⟩]
theorem checked11913 : checkPrefixCuts (2^48) 1565392897 9 Manual.Count131072.C011913.packed 128 cuts11913 = true := by
 decide +kernel
def pointBounds11913 : List (Nat × Nat × Nat) := [(1565434880,93229155255597,93229531117744),(1565484032,93229566645700,93229942508162)]
theorem point_links_checked11913 : (cuts11913.take 2).map (fun c => (1565392897-1+2*2^9*c.k,93228798335555+c.lower,93229174197426+c.upper)) = pointBounds11913 := by
 decide +kernel
def cuts11914 : List PrefixCut := [⟨9,79469579,79469641⟩,
⟨57,493171182,493171564⟩,
⟨105,909196984,909197689⟩,
⟨128,1106418111,1106418967⟩]
theorem checked11914 : checkPrefixCuts (2^48) 1565523969 9 Manual.Count131072.C011914.packed 128 cuts11914 = true := by
 decide +kernel
def pointBounds11914 : List (Nat × Nat × Nat) := [(1565533184,93229982877379,93230358740160),(1565582336,93230396578982,93230772442083),(1565631488,93230812604784,93231188468208)]
theorem point_links_checked11914 : (cuts11914.take 3).map (fun c => (1565523969-1+2*2^9*c.k,93229903407800+c.lower,93230279270519+c.upper)) = pointBounds11914 := by
 decide +kernel
def cuts11915 : List PrefixCut := [⟨25,220948915,220949082⟩,
⟨73,645218127,645218623⟩,
⟨121,1065519124,1065519946⟩,
⟨128,1127718245,1127719113⟩]
theorem checked11915 : checkPrefixCuts (2^48) 1565655041 9 Manual.Count131072.C011915.packed 128 cuts11915 = true := by
 decide +kernel
def pointBounds11915 : List (Nat × Nat × Nat) := [(1565680640,93231230774826,93231606638568),(1565729792,93231655044038,93232030908109),(1565778944,93232075345035,93232451209432)]
theorem point_links_checked11915 : (cuts11915.take 3).map (fun c => (1565655041-1+2*2^9*c.k,93231009825911+c.lower,93231385689486+c.upper)) = pointBounds11915 := by
 decide +kernel
def cuts11916 : List PrefixCut := [⟨41,360785285,360785560⟩,
⟨89,772970897,772971487⟩,
⟨128,1107131868,1107132720⟩]
theorem checked11916 : checkPrefixCuts (2^48) 1565786113 9 Manual.Count131072.C011916.packed 128 cuts11916 = true := by
 decide +kernel
def pointBounds11916 : List (Nat × Nat × Nat) := [(1565828096,93232498329441,93232874194159),(1565877248,93232910515053,93233286380086)]
theorem point_links_checked11916 : (cuts11916.take 2).map (fun c => (1565786113-1+2*2^9*c.k,93232137544156+c.lower,93232513408599+c.upper)) = pointBounds11916 := by
 decide +kernel
def cuts11917 : List PrefixCut := [⟨9,79090117,79090179⟩,
⟨57,498799127,498799507⟩,
⟨105,915619157,915619858⟩,
⟨128,1119441037,1119441893⟩]
theorem checked11917 : checkPrefixCuts (2^48) 1565917185 9 Manual.Count131072.C011917.packed 128 cuts11917 = true := by
 decide +kernel
def pointBounds11917 : List (Nat × Nat × Nat) := [(1565926400,93233323766141,93233699631498),(1565975552,93233743475151,93234119340826),(1566024704,93234160295181,93234536161177)]
theorem point_links_checked11917 : (cuts11917.take 3).map (fun c => (1565917185-1+2*2^9*c.k,93233244676024+c.lower,93233620541319+c.upper)) = pointBounds11917 := by
 decide +kernel
def cuts11918 : List PrefixCut := [⟨25,218377172,218377338⟩,
⟨73,637687289,637687776⟩,
⟨121,1051772211,1051773014⟩,
⟨128,1113416554,1113417404⟩]
theorem checked11918 : checkPrefixCuts (2^48) 1566048257 9 Manual.Count131072.C011918.packed 128 cuts11918 = true := by
 decide +kernel
def pointBounds11918 : List (Nat × Nat × Nat) := [(1566073856,93234582494233,93234958360550),(1566123008,93235001804350,93235377670988),(1566172160,93235415889272,93235791756226)]
theorem point_links_checked11918 : (cuts11918.take 3).map (fun c => (1566048257-1+2*2^9*c.k,93234364117061+c.lower,93234739983212+c.upper)) = pointBounds11918 := by
 decide +kernel
def cuts11919 : List PrefixCut := [⟨41,353326167,353326436⟩,
⟨89,763072053,763072639⟩,
⟨128,1094992713,1094993558⟩]
theorem checked11919 : checkPrefixCuts (2^48) 1566179329 9 Manual.Count131072.C011919.packed 128 cuts11919 = true := by
 decide +kernel
def pointBounds11919 : List (Nat × Nat × Nat) := [(1566221312,93235830859782,93236206727052),(1566270464,93236240605668,93236616473255)]
theorem point_links_checked11919 : (cuts11919.take 2).map (fun c => (1566179329-1+2*2^9*c.k,93235477533615+c.lower,93235853400616+c.upper)) = pointBounds11919 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000059
