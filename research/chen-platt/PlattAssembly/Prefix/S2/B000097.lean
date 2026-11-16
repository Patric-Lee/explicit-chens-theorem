import PlattAssemblyKernel
import PlattCertificates.Count131072.C013104
import PlattCertificates.Count131072.C013105
import PlattCertificates.Count131072.C013106
import PlattCertificates.Count131072.C013107
import PlattCertificates.Count131072.C013108
import PlattCertificates.Count131072.C013109
import PlattCertificates.Count131072.C013110
import PlattCertificates.Count131072.C013111
import PlattCertificates.Count131072.C013112
import PlattCertificates.Count131072.C013113
import PlattCertificates.Count131072.C013114
import PlattCertificates.Count131072.C013115
import PlattCertificates.Count131072.C013116
import PlattCertificates.Count131072.C013117
import PlattCertificates.Count131072.C013118
import PlattCertificates.Count131072.C013119
import PlattCertificates.Count131072.C013120
import PlattCertificates.Count131072.C013121
import PlattCertificates.Count131072.C013122
import PlattCertificates.Count131072.C013123
import PlattCertificates.Count131072.C013124
import PlattCertificates.Count131072.C013125
import PlattCertificates.Count131072.C013126
import PlattCertificates.Count131072.C013127
import PlattCertificates.Count131072.C013128
import PlattCertificates.Count131072.C013129
import PlattCertificates.Count131072.C013130
import PlattCertificates.Count131072.C013131
import PlattCertificates.Count131072.C013132
import PlattCertificates.Count131072.C013133
import PlattCertificates.Count131072.C013134
import PlattCertificates.Count131072.C013135
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000097
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts13104 : List PrefixCut := [⟨13,102681133,102681208⟩,
⟨66,510127608,510127980⟩,
⟨119,930477408,930478086⟩,
⟨128,999635205,999635934⟩]
theorem checked13104 : checkPrefixCuts (2^48) 1721499649 9 Manual.Count131072.C013104.packed 128 cuts13104 = true := by
 decide +kernel
def pointBounds13104 : List (Nat × Nat × Nat) := [(1721512960,94489940787146,94490317588468),(1721567232,94490348233621,94490725035240),(1721621504,94490768583421,94491145385346)]
theorem point_links_checked13104 : (cuts13104.take 3).map (fun c => (1721499649-1+2*2^9*c.k,94489838106013+c.lower,94490214907260+c.upper)) = pointBounds13104 := by
 decide +kernel
def cuts13105 : List PrefixCut := [⟨44,353631084,353631338⟩,
⟨97,759567663,759568217⟩,
⟨128,1002338766,1002339499⟩]
theorem checked13105 : checkPrefixCuts (2^48) 1721630721 9 Manual.Count131072.C013105.packed 128 cuts13105 = true := by
 decide +kernel
def pointBounds13105 : List (Nat × Nat × Nat) := [(1721675776,94491191372302,94491568174532),(1721730048,94491597308881,94491974111411)]
theorem point_links_checked13105 : (cuts13105.take 2).map (fun c => (1721630721-1+2*2^9*c.k,94490837741218+c.lower,94491214543194+c.upper)) = pointBounds13105 := by
 decide +kernel
def cuts13106 : List PrefixCut := [⟨22,176067590,176067716⟩,
⟨75,594893092,594893521⟩,
⟨128,1021388576,1021389314⟩]
theorem checked13106 : checkPrefixCuts (2^48) 1721761793 9 Manual.Count131072.C013106.packed 128 cuts13106 = true := by
 decide +kernel
def pointBounds13106 : List (Nat × Nat × Nat) := [(1721784320,94492016147574,94492392950409),(1721838592,94492434973076,94492811776214),(1721892864,94492861468560,94493238272007)]
theorem point_links_checked13106 : (cuts13106.take 3).map (fun c => (1721761793-1+2*2^9*c.k,94491840079984+c.lower,94492216882693+c.upper)) = pointBounds13106 := by
 decide +kernel
def cuts13107 : List PrefixCut := [⟨53,428607107,428607412⟩,
⟨106,844777683,844778283⟩,
⟨128,1016407431,1016408157⟩]
theorem checked13107 : checkPrefixCuts (2^48) 1721892865 9 Manual.Count131072.C013107.packed 128 cuts13107 = true := by
 decide +kernel
def pointBounds13107 : List (Nat × Nat × Nat) := [(1721947136,94493290075667,94493666879419),(1722001408,94493706246243,94494083050290)]
theorem point_links_checked13107 : (cuts13107.take 2).map (fun c => (1721892865-1+2*2^9*c.k,94492861468560+c.lower,94493238272007+c.upper)) = pointBounds13107 := by
 decide +kernel
def cuts13108 : List PrefixCut := [⟨31,242893171,242893348⟩,
⟨84,658874033,658874513⟩,
⟨128,1004724808,1004725532⟩]
theorem checked13108 : checkPrefixCuts (2^48) 1722023937 9 Manual.Count131072.C013108.packed 128 cuts13108 = true := by
 decide +kernel
def pointBounds13108 : List (Nat × Nat × Nat) := [(1722055680,94494120769162,94494497573512),(1722109952,94494536750024,94494913554677)]
theorem point_links_checked13108 : (cuts13108.take 2).map (fun c => (1722023937-1+2*2^9*c.k,94493877875991+c.lower,94494254680164+c.upper)) = pointBounds13108 := by
 decide +kernel
def cuts13109 : List PrefixCut := [⟨9,73549329,73549381⟩,
⟨62,494407204,494407560⟩,
⟨115,918520585,918521245⟩,
⟨128,1030634654,1030635396⟩]
theorem checked13109 : checkPrefixCuts (2^48) 1722155009 9 Manual.Count131072.C013109.packed 128 cuts13109 = true := by
 decide +kernel
def pointBounds13109 : List (Nat × Nat × Nat) := [(1722164224,94494956150128,94495332955077),(1722218496,94495377008003,94495753813256),(1722272768,94495801121384,94496177926941)]
theorem point_links_checked13109 : (cuts13109.take 3).map (fun c => (1722155009-1+2*2^9*c.k,94494882600799+c.lower,94495259405696+c.upper)) = pointBounds13109 := by
 decide +kernel
def cuts13110 : List PrefixCut := [⟨40,312639731,312639956⟩,
⟨93,727411044,727411570⟩,
⟨128,998688614,998689339⟩]
theorem checked13110 : checkPrefixCuts (2^48) 1722286081 9 Manual.Count131072.C013110.packed 128 cuts13110 = true := by
 decide +kernel
def pointBounds13110 : List (Nat × Nat × Nat) := [(1722327040,94496225875184,94496602681048),(1722381312,94496640646497,94497017452662)]
theorem point_links_checked13110 : (cuts13110.take 2).map (fun c => (1722286081-1+2*2^9*c.k,94495913235453+c.lower,94496290041092+c.upper)) = pointBounds13110 := by
 decide +kernel
def cuts13111 : List PrefixCut := [⟨18,138087914,138088014⟩,
⟨71,550218514,550218909⟩,
⟨124,976552792,976553494⟩,
⟨128,1007763392,1007764118⟩]
theorem checked13111 : checkPrefixCuts (2^48) 1722417153 9 Manual.Count131072.C013111.packed 128 cuts13111 = true := by
 decide +kernel
def pointBounds13111 : List (Nat × Nat × Nat) := [(1722435584,94497050011981,94497426818445),(1722489856,94497462142581,94497838949340),(1722544128,94497888476859,94498265283925)]
theorem point_links_checked13111 : (cuts13111.take 3).map (fun c => (1722417153-1+2*2^9*c.k,94496911924067+c.lower,94497288730431+c.upper)) = pointBounds13111 := by
 decide +kernel
def cuts13112 : List PrefixCut := [⟨49,387266826,387267107⟩,
⟨102,800992487,800993066⟩,
⟨128,996903015,996903733⟩]
theorem checked13112 : checkPrefixCuts (2^48) 1722548225 9 Manual.Count131072.C013112.packed 128 cuts13112 = true := by
 decide +kernel
def pointBounds13112 : List (Nat × Nat × Nat) := [(1722598400,94498306954285,94498683761656),(1722652672,94498720679946,94499097487615)]
theorem point_links_checked13112 : (cuts13112.take 2).map (fun c => (1722548225-1+2*2^9*c.k,94497919687459+c.lower,94498296494549+c.upper)) = pointBounds13112 := by
 decide +kernel
def cuts13113 : List PrefixCut := [⟨27,218128785,218128943⟩,
⟨80,625946358,625946808⟩,
⟨128,1013328755,1013329491⟩]
theorem checked13113 : checkPrefixCuts (2^48) 1722679297 9 Manual.Count131072.C013113.packed 128 cuts13113 = true := by
 decide +kernel
def pointBounds13113 : List (Nat × Nat × Nat) := [(1722706944,94499134719259,94499511527225),(1722761216,94499542536832,94499919345090)]
theorem point_links_checked13113 : (cuts13113.take 2).map (fun c => (1722679297-1+2*2^9*c.k,94498916590474+c.lower,94499293398282+c.upper)) = pointBounds13113 := by
 decide +kernel
def cuts13114 : List PrefixCut := [⟨5,37741007,37741035⟩,
⟨58,451741266,451741593⟩,
⟨111,862951234,862951859⟩,
⟨128,996424206,996424925⟩]
theorem checked13114 : checkPrefixCuts (2^48) 1722810369 9 Manual.Count131072.C013114.packed 128 cuts13114 = true := by
 decide +kernel
def pointBounds13114 : List (Nat × Nat × Nat) := [(1722815488,94499967660236,94500344468808),(1722869760,94500381660495,94500758469366),(1722924032,94500792870463,94501169679632)]
theorem point_links_checked13114 : (cuts13114.take 3).map (fun c => (1722810369-1+2*2^9*c.k,94499929919229+c.lower,94500306727773+c.upper)) = pointBounds13114 := by
 decide +kernel
def cuts13115 : List PrefixCut := [⟨36,277397213,277397418⟩,
⟨89,694135430,694135934⟩,
⟨128,994714644,994715362⟩]
theorem checked13115 : checkPrefixCuts (2^48) 1722941441 9 Manual.Count131072.C013115.packed 128 cuts13115 = true := by
 decide +kernel
def pointBounds13115 : List (Nat × Nat × Nat) := [(1722978304,94501203740648,94501580550116),(1723032576,94501620478865,94501997288632)]
theorem point_links_checked13115 : (cuts13115.take 2).map (fun c => (1722941441-1+2*2^9*c.k,94500926343435+c.lower,94501303152698+c.upper)) = pointBounds13115 := by
 decide +kernel
def cuts13116 : List PrefixCut := [⟨14,111735287,111735368⟩,
⟨67,529100765,529101147⟩,
⟨120,940899314,940899994⟩,
⟨128,1001826750,1001827472⟩]
theorem checked13116 : checkPrefixCuts (2^48) 1723072513 9 Manual.Count131072.C013116.packed 128 cuts13116 = true := by
 decide +kernel
def pointBounds13116 : List (Nat × Nat × Nat) := [(1723086848,94502032793366,94502409603428),(1723141120,94502450158844,94502826969207),(1723195392,94502861957393,94503238768054)]
theorem point_links_checked13116 : (cuts13116.take 3).map (fun c => (1723072513-1+2*2^9*c.k,94501921058079+c.lower,94502297868060+c.upper)) = pointBounds13116 := by
 decide +kernel
def cuts13117 : List PrefixCut := [⟨45,352328212,352328466⟩,
⟨98,773574421,773574979⟩,
⟨128,1003873915,1003874639⟩]
theorem checked13117 : checkPrefixCuts (2^48) 1723203585 9 Manual.Count131072.C013117.packed 128 cuts13117 = true := by
 decide +kernel
def pointBounds13117 : List (Nat × Nat × Nat) := [(1723249664,94503275213041,94503652023998),(1723303936,94503696459250,94504073270511)]
theorem point_links_checked13117 : (cuts13117.take 2).map (fun c => (1723203585-1+2*2^9*c.k,94502922884829+c.lower,94503299695532+c.upper)) = pointBounds13117 := by
 decide +kernel
def cuts13118 : List PrefixCut := [⟨23,181133413,181133542⟩,
⟨76,588960241,588960659⟩,
⟨128,1002817168,1002817886⟩]
theorem checked13118 : checkPrefixCuts (2^48) 1723334657 9 Manual.Count131072.C013118.packed 128 cuts13118 = true := by
 decide +kernel
def pointBounds13118 : List (Nat × Nat × Nat) := [(1723358208,94504107892157,94504484703713),(1723412480,94504515718985,94504892530830)]
theorem point_links_checked13118 : (cuts13118.take 2).map (fun c => (1723334657-1+2*2^9*c.k,94503926758744+c.lower,94504303570171+c.upper)) = pointBounds13118 := by
 decide +kernel
def cuts13119 : List PrefixCut := [⟨1,5879486,5879490⟩,
⟨54,425112776,425113085⟩,
⟨107,833717608,833718213⟩,
⟨128,995392216,995392939⟩]
theorem checked13119 : checkPrefixCuts (2^48) 1723465729 9 Manual.Count131072.C013119.packed 128 cuts13119 = true := by
 decide +kernel
def pointBounds13119 : List (Nat × Nat × Nat) := [(1723466752,94504935455398,94505312267547),(1723521024,94505354688688,94505731501142),(1723575296,94505763293520,94506140106270)]
theorem point_links_checked13119 : (cuts13119.take 3).map (fun c => (1723465729-1+2*2^9*c.k,94504929575912+c.lower,94505306388057+c.upper)) = pointBounds13119 := by
 decide +kernel
def cuts13120 : List PrefixCut := [⟨32,255245936,255246116⟩,
⟨85,676235924,676236405⟩,
⟨128,1014259330,1014260056⟩]
theorem checked13120 : checkPrefixCuts (2^48) 1723596801 9 Manual.Count131072.C013120.packed 128 cuts13120 = true := by
 decide +kernel
def pointBounds13120 : List (Nat × Nat × Nat) := [(1723629568,94506180214064,94506557027112),(1723683840,94506601204052,94506978017401)]
theorem point_links_checked13120 : (cuts13120.take 2).map (fun c => (1723596801-1+2*2^9*c.k,94505924968128+c.lower,94506301780996+c.upper)) = pointBounds13120 := by
 decide +kernel
def cuts13121 : List PrefixCut := [⟨10,74461963,74462016⟩,
⟨63,508162153,508162516⟩,
⟨116,921927942,921928607⟩,
⟨128,1014998930,1014999662⟩]
theorem checked13121 : checkPrefixCuts (2^48) 1723727873 9 Manual.Count131072.C013121.packed 128 cuts13121 = true := by
 decide +kernel
def pointBounds13121 : List (Nat × Nat × Nat) := [(1723738112,94507013689421,94507390503068),(1723792384,94507447389611,94507824203568),(1723846656,94507861155400,94508237969659)]
theorem point_links_checked13121 : (cuts13121.take 3).map (fun c => (1723727873-1+2*2^9*c.k,94506939227458+c.lower,94507316041052+c.upper)) = pointBounds13121 := by
 decide +kernel
def cuts13122 : List PrefixCut := [⟨41,333907307,333907547⟩,
⟨94,747483681,747484218⟩,
⟨128,1019983168,1019983907⟩]
theorem checked13122 : checkPrefixCuts (2^48) 1723858945 9 Manual.Count131072.C013122.packed 128 cuts13122 = true := by
 decide +kernel
def pointBounds13122 : List (Nat × Nat × Nat) := [(1723900928,94508288133695,94508664948261),(1723955200,94508701710069,94509078524932)]
theorem point_links_checked13122 : (cuts13122.take 2).map (fun c => (1723858945-1+2*2^9*c.k,94507954226388+c.lower,94508331040714+c.upper)) = pointBounds13122 := by
 decide +kernel
def cuts13123 : List PrefixCut := [⟨19,145308988,145309098⟩,
⟨72,561308253,561308665⟩,
⟨125,977784241,977784958⟩,
⟨128,1000476987,1000477721⟩]
theorem checked13123 : checkPrefixCuts (2^48) 1723990017 9 Manual.Count131072.C013123.packed 128 cuts13123 = true := by
 decide +kernel
def pointBounds13123 : List (Nat × Nat × Nat) := [(1724009472,94509119518544,94509496333719),(1724063744,94509535517809,94509912333286),(1724118016,94509951993797,94510328809579)]
theorem point_links_checked13123 : (cuts13123.take 3).map (fun c => (1723990017-1+2*2^9*c.k,94508974209556+c.lower,94509351024621+c.upper)) = pointBounds13123 := by
 decide +kernel
def cuts13124 : List PrefixCut := [⟨50,396382252,396382532⟩,
⟨103,812831929,812832509⟩,
⟨128,1004972287,1004973006⟩]
theorem checked13124 : checkPrefixCuts (2^48) 1724121089 9 Manual.Count131072.C013124.packed 128 cuts13124 = true := by
 decide +kernel
def pointBounds13124 : List (Nat × Nat × Nat) := [(1724172288,94510371068795,94510747884874),(1724226560,94510787518472,94511164334851)]
theorem point_links_checked13124 : (cuts13124.take 2).map (fun c => (1724121089-1+2*2^9*c.k,94509974686543+c.lower,94510351502342+c.upper)) = pointBounds13124 := by
 decide +kernel
def cuts13125 : List PrefixCut := [⟨28,223316791,223316948⟩,
⟨81,632231260,632231716⟩,
⟨128,986123587,986124302⟩]
theorem checked13125 : checkPrefixCuts (2^48) 1724252161 9 Manual.Count131072.C013125.packed 128 cuts13125 = true := by
 decide +kernel
def pointBounds13125 : List (Nat × Nat × Nat) := [(1724280832,94511202975621,94511579792296),(1724335104,94511611890090,94511988707064)]
theorem point_links_checked13125 : (cuts13125.take 2).map (fun c => (1724252161-1+2*2^9*c.k,94510979658830+c.lower,94511356475348+c.upper)) = pointBounds13125 := by
 decide +kernel
def cuts13126 : List PrefixCut := [⟨6,45868169,45868201⟩,
⟨59,470426870,470427207⟩,
⟨112,896278132,896278772⟩,
⟨128,1026528140,1026528873⟩]
theorem checked13126 : checkPrefixCuts (2^48) 1724383233 9 Manual.Count131072.C013126.packed 128 cuts13126 = true := by
 decide +kernel
def pointBounds13126 : List (Nat × Nat × Nat) := [(1724389376,94512011650586,94512388467851),(1724443648,94512436209287,94512813026857),(1724497920,94512862060549,94513238878422)]
theorem point_links_checked13126 : (cuts13126.take 3).map (fun c => (1724383233-1+2*2^9*c.k,94511965782417+c.lower,94512342599650+c.upper)) = pointBounds13126 := by
 decide +kernel
def cuts13127 : List PrefixCut := [⟨37,282040679,282040884⟩,
⟨90,694971284,694971785⟩,
⟨128,994949890,994950609⟩]
theorem checked13127 : checkPrefixCuts (2^48) 1724514305 9 Manual.Count131072.C013127.packed 128 cuts13127 = true := by
 decide +kernel
def pointBounds13127 : List (Nat × Nat × Nat) := [(1724552192,94513274351236,94513651169407),(1724606464,94513687281841,94514064100308)]
theorem point_links_checked13127 : (cuts13127.take 2).map (fun c => (1724514305-1+2*2^9*c.k,94512992310557+c.lower,94513369128523+c.upper)) = pointBounds13127 := by
 decide +kernel
def cuts13128 : List PrefixCut := [⟨15,121262547,121262633⟩,
⟨68,546244098,546244487⟩,
⟨121,963052410,963053100⟩,
⟨128,1017233255,1017233985⟩]
theorem checked13128 : checkPrefixCuts (2^48) 1724645377 9 Manual.Count131072.C013128.packed 128 cuts13128 = true := by
 decide +kernel
def pointBounds13128 : List (Nat × Nat × Nat) := [(1724660736,94514108522994,94514485341765),(1724715008,94514533504545,94514910323619),(1724769280,94514950312857,94515327132232)]
theorem point_links_checked13128 : (cuts13128.take 3).map (fun c => (1724645377-1+2*2^9*c.k,94513987260447+c.lower,94514364079132+c.upper)) = pointBounds13128 := by
 decide +kernel
def cuts13129 : List PrefixCut := [⟨46,360329641,360329905⟩,
⟨99,782496872,782497438⟩,
⟨128,1008017147,1008017874⟩]
theorem checked13129 : checkPrefixCuts (2^48) 1724776449 9 Manual.Count131072.C013129.packed 128 cuts13129 = true := by
 decide +kernel
def pointBounds13129 : List (Nat × Nat × Nat) := [(1724823552,94515364823343,94515741643022),(1724877824,94515786990574,94516163810555)]
theorem point_links_checked13129 : (cuts13129.take 2).map (fun c => (1724776449-1+2*2^9*c.k,94515004493702+c.lower,94515381313117+c.upper)) = pointBounds13129 := by
 decide +kernel
def cuts13130 : List PrefixCut := [⟨24,185374105,185374239⟩,
⟨77,596745054,596745488⟩,
⟨128,990154388,990155107⟩]
theorem checked13130 : checkPrefixCuts (2^48) 1724907521 9 Manual.Count131072.C013130.packed 128 cuts13130 = true := by
 decide +kernel
def pointBounds13130 : List (Nat × Nat × Nat) := [(1724932096,94516197884954,94516574705230),(1724986368,94516609255903,94516986076479)]
theorem point_links_checked13130 : (cuts13130.take 2).map (fun c => (1724907521-1+2*2^9*c.k,94516012510849+c.lower,94516389330991+c.upper)) = pointBounds13130 := by
 decide +kernel
def cuts13131 : List PrefixCut := [⟨2,15337989,15338000⟩,
⟨55,428804246,428804556⟩,
⟨108,840136399,840137004⟩,
⟨128,1002316216,1002316939⟩]
theorem checked13131 : checkPrefixCuts (2^48) 1725038593 9 Manual.Count131072.C013131.packed 128 cuts13131 = true := by
 decide +kernel
def pointBounds13131 : List (Nat × Nat × Nat) := [(1725040640,94517018003226,94517394824098),(1725094912,94517431469483,94517808290654),(1725149184,94517842801636,94518219623102)]
theorem point_links_checked13131 : (cuts13131.take 3).map (fun c => (1725038593-1+2*2^9*c.k,94517002665237+c.lower,94517379486098+c.upper)) = pointBounds13131 := by
 decide +kernel
def cuts13132 : List PrefixCut := [⟨33,254197335,254197520⟩,
⟨86,659793277,659793754⟩,
⟨128,994082400,994083120⟩]
theorem checked13132 : checkPrefixCuts (2^48) 1725169665 9 Manual.Count131072.C013132.packed 128 cuts13132 = true := by
 decide +kernel
def pointBounds13132 : List (Nat × Nat × Nat) := [(1725203456,94518259178788,94518636000557),(1725257728,94518664774730,94519041596791)]
theorem point_links_checked13132 : (cuts13132.take 2).map (fun c => (1725169665-1+2*2^9*c.k,94518004981453+c.lower,94518381803037+c.upper)) = pointBounds13132 := by
 decide +kernel
def cuts13133 : List PrefixCut := [⟨11,83203877,83203938⟩,
⟨64,508514485,508514853⟩,
⟨117,927286203,927286870⟩,
⟨128,1015378320,1015379051⟩]
theorem checked13133 : checkPrefixCuts (2^48) 1725300737 9 Manual.Count131072.C013133.packed 128 cuts13133 = true := by
 decide +kernel
def pointBounds13133 : List (Nat × Nat × Nat) := [(1725312000,94519082267730,94519459090095),(1725366272,94519507578338,94519884401010),(1725420544,94519926350056,94520303173027)]
theorem point_links_checked13133 : (cuts13133.take 3).map (fun c => (1725300737-1+2*2^9*c.k,94518999063853+c.lower,94519375886157+c.upper)) = pointBounds13133 := by
 decide +kernel
def cuts13134 : List PrefixCut := [⟨42,327566988,327567227⟩,
⟨95,736198526,736199062⟩,
⟨128,996052172,996052897⟩]
theorem checked13134 : checkPrefixCuts (2^48) 1725431809 9 Manual.Count131072.C013134.packed 128 cuts13134 = true := by
 decide +kernel
def pointBounds13134 : List (Nat × Nat × Nat) := [(1725474816,94520342009161,94520718832435),(1725529088,94520750640699,94521127464270)]
theorem point_links_checked13134 : (cuts13134.take 2).map (fun c => (1725431809-1+2*2^9*c.k,94520014442173+c.lower,94520391265208+c.upper)) = pointBounds13134 := by
 decide +kernel
def cuts13135 : List PrefixCut := [⟨20,158062926,158063039⟩,
⟨73,573193444,573193857⟩,
⟨126,981786391,981787098⟩,
⟨128,996955465,996956183⟩]
theorem checked13135 : checkPrefixCuts (2^48) 1725562881 9 Manual.Count131072.C013135.packed 128 cuts13135 = true := by
 decide +kernel
def pointBounds13135 : List (Nat × Nat × Nat) := [(1725583360,94521168557271,94521545381144),(1725637632,94521583687789,94521960511962),(1725691904,94521992280736,94522369105203)]
theorem point_links_checked13135 : (cuts13135.take 3).map (fun c => (1725562881-1+2*2^9*c.k,94521010494345+c.lower,94521387318105+c.upper)) = pointBounds13135 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000097
