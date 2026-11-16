import PlattAssemblyKernel
import PlattCertificates.Count131072.C019600
import PlattCertificates.Count131072.C019601
import PlattCertificates.Count131072.C019602
import PlattCertificates.Count131072.C019603
import PlattCertificates.Count131072.C019604
import PlattCertificates.Count131072.C019605
import PlattCertificates.Count131072.C019606
import PlattCertificates.Count131072.C019607
import PlattCertificates.Count131072.C019608
import PlattCertificates.Count131072.C019609
import PlattCertificates.Count131072.C019610
import PlattCertificates.Count131072.C019611
import PlattCertificates.Count131072.C019612
import PlattCertificates.Count131072.C019613
import PlattCertificates.Count131072.C019614
import PlattCertificates.Count131072.C019615
import PlattCertificates.Count131072.C019616
import PlattCertificates.Count131072.C019617
import PlattCertificates.Count131072.C019618
import PlattCertificates.Count131072.C019619
import PlattCertificates.Count131072.C019620
import PlattCertificates.Count131072.C019621
import PlattCertificates.Count131072.C019622
import PlattCertificates.Count131072.C019623
import PlattCertificates.Count131072.C019624
import PlattCertificates.Count131072.C019625
import PlattCertificates.Count131072.C019626
import PlattCertificates.Count131072.C019627
import PlattCertificates.Count131072.C019628
import PlattCertificates.Count131072.C019629
import PlattCertificates.Count131072.C019630
import PlattCertificates.Count131072.C019631
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000300
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts19600 : List PrefixCut := [⟨79,412642826,412643072⟩,
⟨128,665998169,665998568⟩]
theorem checked19600 : checkPrefixCuts (2^48) 2572943361 9 Manual.Count131072.C019600.packed 128 cuts19600 = true := by
 decide +kernel
def pointBounds19600 : List (Nat × Nat × Nat) := [(2573024256,99759376915505,99759757131038)]
theorem point_links_checked19600 : (cuts19600.take 1).map (fun c => (2572943361-1+2*2^9*c.k,99758964272679+c.lower,99759344487966+c.upper)) = pointBounds19600 := by
 decide +kernel
def cuts19601 : List PrefixCut := [⟨30,149976148,149976235⟩,
⟨109,558107991,558108319⟩,
⟨128,656118998,656119382⟩]
theorem checked19601 : checkPrefixCuts (2^48) 2573074433 9 Manual.Count131072.C019601.packed 128 cuts19601 = true := by
 decide +kernel
def pointBounds19601 : List (Nat × Nat × Nat) := [(2573105152,99759780246996,99760160462769),(2573186048,99760188378839,99760568594853)]
theorem point_links_checked19601 : (cuts19601.take 2).map (fun c => (2573074433-1+2*2^9*c.k,99759630270848+c.lower,99760010486534+c.upper)) = pointBounds19601 := by
 decide +kernel
def cuts19602 : List PrefixCut := [⟨60,311967611,311967790⟩,
⟨128,654773208,654773596⟩]
theorem checked19602 : checkPrefixCuts (2^48) 2573205505 9 Manual.Count131072.C019602.packed 128 cuts19602 = true := by
 decide +kernel
def pointBounds19602 : List (Nat × Nat × Nat) := [(2573266944,99760598357457,99760978573706)]
theorem point_links_checked19602 : (cuts19602.take 1).map (fun c => (2573205505-1+2*2^9*c.k,99760286389846+c.lower,99760666605916+c.upper)) = pointBounds19602 := by
 decide +kernel
def cuts19603 : List PrefixCut := [⟨11,57096912,57096947⟩,
⟨90,472081191,472081470⟩,
⟨128,669177734,669178131⟩]
theorem checked19603 : checkPrefixCuts (2^48) 2573336577 9 Manual.Count131072.C019603.packed 128 cuts19603 = true := by
 decide +kernel
def pointBounds19603 : List (Nat × Nat × Nat) := [(2573347840,99760998259966,99761378476459),(2573428736,99761413244245,99761793460982)]
theorem point_links_checked19603 : (cuts19603.take 2).map (fun c => (2573336577-1+2*2^9*c.k,99760941163054+c.lower,99761321379512+c.upper)) = pointBounds19603 := by
 decide +kernel
def cuts19604 : List PrefixCut := [⟨41,210874656,210874783⟩,
⟨120,618395541,618395917⟩,
⟨128,659956265,659956665⟩]
theorem checked19604 : checkPrefixCuts (2^48) 2573467649 9 Manual.Count131072.C019604.packed 128 cuts19604 = true := by
 decide +kernel
def pointBounds19604 : List (Nat × Nat × Nat) := [(2573509632,99761821215444,99762201432426),(2573590528,99762228736329,99762608953560)]
theorem point_links_checked19604 : (cuts19604.take 2).map (fun c => (2573467649-1+2*2^9*c.k,99761610340788+c.lower,99761990557643+c.upper)) = pointBounds19604 := by
 decide +kernel
def cuts19605 : List PrefixCut := [⟨71,368462796,368463013⟩,
⟨128,665828467,665828863⟩]
theorem checked19605 : checkPrefixCuts (2^48) 2573598721 9 Manual.Count131072.C019605.packed 128 cuts19605 = true := by
 decide +kernel
def pointBounds19605 : List (Nat × Nat × Nat) := [(2573671424,99762638759849,99763018977321)]
theorem point_links_checked19605 : (cuts19605.take 1).map (fun c => (2573598721-1+2*2^9*c.k,99762270297053+c.lower,99762650514308+c.upper)) = pointBounds19605 := by
 decide +kernel
def cuts19606 : List PrefixCut := [⟨22,113082488,113082557⟩,
⟨101,517830882,517831192⟩,
⟨128,659342212,659342607⟩]
theorem checked19606 : checkPrefixCuts (2^48) 2573729793 9 Manual.Count131072.C019606.packed 128 cuts19606 = true := by
 decide +kernel
def pointBounds19606 : List (Nat × Nat × Nat) := [(2573752320,99763049208008,99763429425728),(2573833216,99763453956402,99763834174363)]
theorem point_links_checked19606 : (cuts19606.take 2).map (fun c => (2573729793-1+2*2^9*c.k,99762936125520+c.lower,99763316343171+c.upper)) = pointBounds19606 := by
 decide +kernel
def cuts19607 : List PrefixCut := [⟨52,275800600,275800763⟩,
⟨128,661058646,661059036⟩]
theorem checked19607 : checkPrefixCuts (2^48) 2573860865 9 Manual.Count131072.C019607.packed 128 cuts19607 = true := by
 decide +kernel
def pointBounds19607 : List (Nat × Nat × Nat) := [(2573914112,99763871268332,99764251486541)]
theorem point_links_checked19607 : (cuts19607.take 1).map (fun c => (2573860865-1+2*2^9*c.k,99763595467732+c.lower,99763975685778+c.upper)) = pointBounds19607 := by
 decide +kernel
def cuts19608 : List PrefixCut := [⟨3,14872060,14872069⟩,
⟨82,423081579,423081832⟩,
⟨128,668460471,668460871⟩]
theorem checked19608 : checkPrefixCuts (2^48) 2573991937 9 Manual.Count131072.C019608.packed 128 cuts19608 = true := by
 decide +kernel
def pointBounds19608 : List (Nat × Nat × Nat) := [(2573995008,99764271398438,99764651616883),(2574075904,99764679607957,99765059826646)]
theorem point_links_checked19608 : (cuts19608.take 2).map (fun c => (2573991937-1+2*2^9*c.k,99764256526378+c.lower,99764636744814+c.upper)) = pointBounds19608 := by
 decide +kernel
def cuts19609 : List PrefixCut := [⟨33,167082466,167082567⟩,
⟨112,574828975,574829314⟩,
⟨128,657929396,657929781⟩]
theorem checked19609 : checkPrefixCuts (2^48) 2574123009 9 Manual.Count131072.C019609.packed 128 cuts19609 = true := by
 decide +kernel
def pointBounds19609 : List (Nat × Nat × Nat) := [(2574156800,99765092069315,99765472288252),(2574237696,99765499815824,99765880034999)]
theorem point_links_checked19609 : (cuts19609.take 2).map (fun c => (2574123009-1+2*2^9*c.k,99764924986849+c.lower,99765305205685+c.upper)) = pointBounds19609 := by
 decide +kernel
def cuts19610 : List PrefixCut := [⟨63,329662941,329663141⟩,
⟨128,658552134,658552534⟩]
theorem checked19610 : checkPrefixCuts (2^48) 2574254081 9 Manual.Count131072.C019610.packed 128 cuts19610 = true := by
 decide +kernel
def pointBounds19610 : List (Nat × Nat × Nat) := [(2574318592,99765912579186,99766292798607)]
theorem point_links_checked19610 : (cuts19610.take 1).map (fun c => (2574254081-1+2*2^9*c.k,99765582916245+c.lower,99765963135466+c.upper)) = pointBounds19610 := by
 decide +kernel
def cuts19611 : List PrefixCut := [⟨14,71178023,71178068⟩,
⟨93,478448812,478449094⟩,
⟨128,666171743,666172138⟩]
theorem checked19611 : checkPrefixCuts (2^48) 2574385153 9 Manual.Count131072.C019611.packed 128 cuts19611 = true := by
 decide +kernel
def pointBounds19611 : List (Nat × Nat × Nat) := [(2574399488,99766312646402,99766692866068),(2574480384,99766719917191,99767100137094)]
theorem point_links_checked19611 : (cuts19611.take 2).map (fun c => (2574385153-1+2*2^9*c.k,99766241468379+c.lower,99766621688000+c.upper)) = pointBounds19611 := by
 decide +kernel
def cuts19612 : List PrefixCut := [⟨44,224017606,224017742⟩,
⟨123,632356074,632356456⟩,
⟨128,659796831,659797229⟩]
theorem checked19612 : checkPrefixCuts (2^48) 2574516225 9 Manual.Count131072.C019612.packed 128 cuts19612 = true := by
 decide +kernel
def pointBounds19612 : List (Nat × Nat × Nat) := [(2574561280,99767131657728,99767511877880),(2574642176,99767539996196,99767920216594)]
theorem point_links_checked19612 : (cuts19612.take 2).map (fun c => (2574516225-1+2*2^9*c.k,99766907640122+c.lower,99767287860138+c.upper)) = pointBounds19612 := by
 decide +kernel
def cuts19613 : List PrefixCut := [⟨74,389958750,389958984⟩,
⟨128,668946516,668946917⟩]
theorem checked19613 : checkPrefixCuts (2^48) 2574647297 9 Manual.Count131072.C019613.packed 128 cuts19613 = true := by
 decide +kernel
def pointBounds19613 : List (Nat × Nat × Nat) := [(2574723072,99767957395703,99768337616351)]
theorem point_links_checked19613 : (cuts19613.take 1).map (fun c => (2574647297-1+2*2^9*c.k,99767567436953+c.lower,99767947657367+c.upper)) = pointBounds19613 := by
 decide +kernel
def cuts19614 : List PrefixCut := [⟨25,131948645,131948722⟩,
⟨104,538608769,538609080⟩,
⟨128,661588148,661588531⟩]
theorem checked19614 : checkPrefixCuts (2^48) 2574778369 9 Manual.Count131072.C019614.packed 128 cuts19614 = true := by
 decide +kernel
def pointBounds19614 : List (Nat × Nat × Nat) := [(2574803968,99768368332114,99768748553006),(2574884864,99768774992238,99769155213364)]
theorem point_links_checked19614 : (cuts19614.take 2).map (fun c => (2574778369-1+2*2^9*c.k,99768236383469+c.lower,99768616604284+c.upper)) = pointBounds19614 := by
 decide +kernel
def cuts19615 : List PrefixCut := [⟨55,290117442,290117611⟩,
⟨128,657837961,657838351⟩]
theorem checked19615 : checkPrefixCuts (2^48) 2574909441 9 Manual.Count131072.C019615.packed 128 cuts19615 = true := by
 decide +kernel
def pointBounds19615 : List (Nat × Nat × Nat) := [(2574965760,99769188089059,99769568310426)]
theorem point_links_checked19615 : (cuts19615.take 1).map (fun c => (2574909441-1+2*2^9*c.k,99768897971617+c.lower,99769278192815+c.upper)) = pointBounds19615 := by
 decide +kernel
def cuts19616 : List PrefixCut := [⟨6,30934386,30934404⟩,
⟨85,447503143,447503408⟩,
⟨128,665346581,665346979⟩]
theorem checked19616 : checkPrefixCuts (2^48) 2575040513 9 Manual.Count131072.C019616.packed 128 cuts19616 = true := by
 decide +kernel
def pointBounds19616 : List (Nat × Nat × Nat) := [(2575046656,99769586743964,99769966965570),(2575127552,99770003312721,99770383534574)]
theorem point_links_checked19616 : (cuts19616.take 2).map (fun c => (2575040513-1+2*2^9*c.k,99769555809578+c.lower,99769936031166+c.upper)) = pointBounds19616 := by
 decide +kernel
def cuts19617 : List PrefixCut := [⟨36,186688780,186688889⟩,
⟨115,592301309,592301653⟩,
⟨128,659301024,659301408⟩]
theorem checked19617 : checkPrefixCuts (2^48) 2575171585 9 Manual.Count131072.C019617.packed 128 cuts19617 = true := by
 decide +kernel
def pointBounds19617 : List (Nat × Nat × Nat) := [(2575208448,99770407844939,99770788067034),(2575289344,99770813457468,99771193679798)]
theorem point_links_checked19617 : (cuts19617.take 2).map (fun c => (2575171585-1+2*2^9*c.k,99770221156159+c.lower,99770601378145+c.upper)) = pointBounds19617 := by
 decide +kernel
def cuts19618 : List PrefixCut := [⟨66,341441823,341442026⟩,
⟨128,661016247,661016640⟩]
theorem checked19618 : checkPrefixCuts (2^48) 2575302657 9 Manual.Count131072.C019618.packed 128 cuts19618 = true := by
 decide +kernel
def pointBounds19618 : List (Nat × Nat × Nat) := [(2575370240,99771221899006,99771602121579)]
theorem point_links_checked19618 : (cuts19618.take 1).map (fun c => (2575302657-1+2*2^9*c.k,99770880457183+c.lower,99771260679553+c.upper)) = pointBounds19618 := by
 decide +kernel
def cuts19619 : List PrefixCut := [⟨17,86121983,86122034⟩,
⟨96,496177209,496177499⟩,
⟨128,659233959,659234349⟩]
theorem checked19619 : checkPrefixCuts (2^48) 2575433729 9 Manual.Count131072.C019619.packed 128 cuts19619 = true := by
 decide +kernel
def pointBounds19619 : List (Nat × Nat × Nat) := [(2575451136,99771627595413,99772007818227),(2575532032,99772037650639,99772417873692)]
theorem point_links_checked19619 : (cuts19619.take 2).map (fun c => (2575433729-1+2*2^9*c.k,99771541473430+c.lower,99771921696193+c.upper)) = pointBounds19619 := by
 decide +kernel
def cuts19620 : List PrefixCut := [⟨47,247750545,247750690⟩,
⟨126,654283012,654283397⟩,
⟨128,664118315,664118706⟩]
theorem checked19620 : checkPrefixCuts (2^48) 2575564801 9 Manual.Count131072.C019620.packed 128 cuts19620 = true := by
 decide +kernel
def pointBounds19620 : List (Nat × Nat × Nat) := [(2575612928,99772448457934,99772828681232),(2575693824,99772854990401,99773235213939)]
theorem point_links_checked19620 : (cuts19620.take 2).map (fun c => (2575564801-1+2*2^9*c.k,99772200707389+c.lower,99772580930542+c.upper)) = pointBounds19620 := by
 decide +kernel
def cuts19621 : List PrefixCut := [⟨77,404006078,404006322⟩,
⟨128,665395820,665396224⟩]
theorem checked19621 : checkPrefixCuts (2^48) 2575695873 9 Manual.Count131072.C019621.packed 128 cuts19621 = true := by
 decide +kernel
def pointBounds19621 : List (Nat × Nat × Nat) := [(2575774720,99773268831782,99773649055570)]
theorem point_links_checked19621 : (cuts19621.take 1).map (fun c => (2575695873-1+2*2^9*c.k,99772864825704+c.lower,99773245049248+c.upper)) = pointBounds19621 := by
 decide +kernel
def cuts19622 : List PrefixCut := [⟨28,140855390,140855476⟩,
⟨107,552594620,552594951⟩,
⟨128,658149861,658150255⟩]
theorem checked19622 : checkPrefixCuts (2^48) 2575826945 9 Manual.Count131072.C019622.packed 128 cuts19622 = true := by
 decide +kernel
def pointBounds19622 : List (Nat × Nat × Nat) := [(2575855616,99773671076914,99774051300948),(2575936512,99774082816144,99774463040423)]
theorem point_links_checked19622 : (cuts19622.take 2).map (fun c => (2575826945-1+2*2^9*c.k,99773530221524+c.lower,99773910445472+c.upper)) = pointBounds19622 := by
 decide +kernel
def cuts19623 : List PrefixCut := [⟨58,296446039,296446211⟩,
⟨128,653745673,653746058⟩]
theorem checked19623 : checkPrefixCuts (2^48) 2575958017 9 Manual.Count131072.C019623.packed 128 cuts19623 = true := by
 decide +kernel
def pointBounds19623 : List (Nat × Nat × Nat) := [(2576017408,99774484817424,99774865041938)]
theorem point_links_checked19623 : (cuts19623.take 1).map (fun c => (2575958017-1+2*2^9*c.k,99774188371385+c.lower,99774568595727+c.upper)) = pointBounds19623 := by
 decide +kernel
def cuts19624 : List PrefixCut := [⟨9,46109502,46109531⟩,
⟨88,458574731,458575008⟩,
⟨128,664966364,664966767⟩]
theorem checked19624 : checkPrefixCuts (2^48) 2576089089 9 Manual.Count131072.C019624.packed 128 cuts19624 = true := by
 decide +kernel
def pointBounds19624 : List (Nat × Nat × Nat) := [(2576098304,99774888226560,99775268451316),(2576179200,99775300691789,99775680916793)]
theorem point_links_checked19624 : (cuts19624.take 2).map (fun c => (2576089089-1+2*2^9*c.k,99774842117058+c.lower,99775222341785+c.upper)) = pointBounds19624 := by
 decide +kernel
def cuts19625 : List PrefixCut := [⟨39,203656958,203657077⟩,
⟨118,611507551,611507914⟩,
⟨128,662856710,662857102⟩]
theorem checked19625 : checkPrefixCuts (2^48) 2576220161 9 Manual.Count131072.C019625.packed 128 cuts19625 = true := by
 decide +kernel
def pointBounds19625 : List (Nat × Nat × Nat) := [(2576260096,99775710740380,99776090965629),(2576340992,99776118590973,99776498816466)]
theorem point_links_checked19625 : (cuts19625.take 2).map (fun c => (2576220161-1+2*2^9*c.k,99775507083422+c.lower,99775887308552+c.upper)) = pointBounds19625 := by
 decide +kernel
def cuts19626 : List PrefixCut := [⟨69,360093964,360094182⟩,
⟨128,667302240,667302641⟩]
theorem checked19626 : checkPrefixCuts (2^48) 2576351233 9 Manual.Count131072.C019626.packed 128 cuts19626 = true := by
 decide +kernel
def pointBounds19626 : List (Nat × Nat × Nat) := [(2576421888,99776530034096,99776910259836)]
theorem point_links_checked19626 : (cuts19626.take 1).map (fun c => (2576351233-1+2*2^9*c.k,99776169940132+c.lower,99776550165654+c.upper)) = pointBounds19626 := by
 decide +kernel
def cuts19627 : List PrefixCut := [⟨20,103675705,103675766⟩,
⟨99,514546727,514547036⟩,
⟨128,663663182,663663581⟩]
theorem checked19627 : checkPrefixCuts (2^48) 2576482305 9 Manual.Count131072.C019627.packed 128 cuts19627 = true := by
 decide +kernel
def pointBounds19627 : List (Nat × Nat × Nat) := [(2576502784,99776940918077,99777321144061),(2576583680,99777351789099,99777732015331)]
theorem point_links_checked19627 : (cuts19627.take 2).map (fun c => (2576482305-1+2*2^9*c.k,99776837242372+c.lower,99777217468295+c.upper)) = pointBounds19627 := by
 decide +kernel
def cuts19628 : List PrefixCut := [⟨50,255514945,255515097⟩,
⟨128,658385852,658386240⟩]
theorem checked19628 : checkPrefixCuts (2^48) 2576613377 9 Manual.Count131072.C019628.packed 128 cuts19628 = true := by
 decide +kernel
def pointBounds19628 : List (Nat × Nat × Nat) := [(2576664576,99777756420499,99778136646973)]
theorem point_links_checked19628 : (cuts19628.take 1).map (fun c => (2576613377-1+2*2^9*c.k,99777500905554+c.lower,99777881131876+c.upper)) = pointBounds19628 := by
 decide +kernel
def cuts19629 : List PrefixCut := [⟨1,4587938,4587941⟩,
⟨80,409958597,409958839⟩,
⟨128,653873936,653874322⟩]
theorem checked19629 : checkPrefixCuts (2^48) 2576744449 9 Manual.Count131072.C019629.packed 128 cuts19629 = true := by
 decide +kernel
def pointBounds19629 : List (Nat × Nat × Nat) := [(2576745472,99778163879344,99778544106057),(2576826368,99778569250003,99778949476955)]
theorem point_links_checked19629 : (cuts19629.take 2).map (fun c => (2576744449-1+2*2^9*c.k,99778159291406+c.lower,99778539518116+c.upper)) = pointBounds19629 := by
 decide +kernel
def cuts19630 : List PrefixCut := [⟨31,154342547,154342640⟩,
⟨110,566022902,566023236⟩,
⟨128,659738731,659739122⟩]
theorem checked19630 : checkPrefixCuts (2^48) 2576875521 9 Manual.Count131072.C019630.packed 128 cuts19630 = true := by
 decide +kernel
def pointBounds19630 : List (Nat × Nat × Nat) := [(2576907264,99778967507889,99779347735078),(2576988160,99779379188244,99779759415674)]
theorem point_links_checked19630 : (cuts19630.take 2).map (fun c => (2576875521-1+2*2^9*c.k,99778813165342+c.lower,99779193392438+c.upper)) = pointBounds19630 := by
 decide +kernel
def cuts19631 : List PrefixCut := [⟨61,309759860,309760041⟩,
⟨128,657411628,657412013⟩]
theorem checked19631 : checkPrefixCuts (2^48) 2577006593 9 Manual.Count131072.C019631.packed 128 cuts19631 = true := by
 decide +kernel
def pointBounds19631 : List (Nat × Nat × Nat) := [(2577069056,99779782663933,99780162891601)]
theorem point_links_checked19631 : (cuts19631.take 1).map (fun c => (2577006593-1+2*2^9*c.k,99779472904073+c.lower,99779853131560+c.upper)) = pointBounds19631 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000300
