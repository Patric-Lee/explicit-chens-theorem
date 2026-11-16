import PlattAssemblyKernel
import PlattCertificates.Count131072.C011920
import PlattCertificates.Count131072.C011921
import PlattCertificates.Count131072.C011922
import PlattCertificates.Count131072.C011923
import PlattCertificates.Count131072.C011924
import PlattCertificates.Count131072.C011925
import PlattCertificates.Count131072.C011926
import PlattCertificates.Count131072.C011927
import PlattCertificates.Count131072.C011928
import PlattCertificates.Count131072.C011929
import PlattCertificates.Count131072.C011930
import PlattCertificates.Count131072.C011931
import PlattCertificates.Count131072.C011932
import PlattCertificates.Count131072.C011933
import PlattCertificates.Count131072.C011934
import PlattCertificates.Count131072.C011935
import PlattCertificates.Count131072.C011936
import PlattCertificates.Count131072.C011937
import PlattCertificates.Count131072.C011938
import PlattCertificates.Count131072.C011939
import PlattCertificates.Count131072.C011940
import PlattCertificates.Count131072.C011941
import PlattCertificates.Count131072.C011942
import PlattCertificates.Count131072.C011943
import PlattCertificates.Count131072.C011944
import PlattCertificates.Count131072.C011945
import PlattCertificates.Count131072.C011946
import PlattCertificates.Count131072.C011947
import PlattCertificates.Count131072.C011948
import PlattCertificates.Count131072.C011949
import PlattCertificates.Count131072.C011950
import PlattCertificates.Count131072.C011951
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000060
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts11920 : List PrefixCut := [⟨9,77812334,77812392⟩,
⟨57,493103289,493103666⟩,
⟨105,908381135,908381833⟩,
⟨128,1109097078,1109097930⟩]
theorem checked11920 : checkPrefixCuts (2^48) 1566310401 9 Manual.Count131072.C011920.packed 128 cuts11920 = true := by
 decide +kernel
def pointBounds11920 : List (Nat × Nat × Nat) := [(1566319616,93236650338662,93237026206566),(1566368768,93237065629617,93237441497840),(1566417920,93237480907463,93237856776007)]
theorem point_links_checked11920 : (cuts11920.take 3).map (fun c => (1566310401-1+2*2^9*c.k,93236572526328+c.lower,93236948394174+c.upper)) = pointBounds11920 := by
 decide +kernel
def cuts11921 : List PrefixCut := [⟨25,212572246,212572409⟩,
⟨73,637347422,637347909⟩,
⟨121,1055281273,1055282082⟩,
⟨128,1114933709,1114934564⟩]
theorem checked11921 : checkPrefixCuts (2^48) 1566441473 9 Manual.Count131072.C011921.packed 128 cuts11921 = true := by
 decide +kernel
def pointBounds11921 : List (Nat × Nat × Nat) := [(1566467072,93237894195652,93238270064513),(1566516224,93238318970828,93238694840013),(1566565376,93238736904679,93239112774186)]
theorem point_links_checked11921 : (cuts11921.take 3).map (fun c => (1566441473-1+2*2^9*c.k,93237681623406+c.lower,93238057492104+c.upper)) = pointBounds11921 := by
 decide +kernel
def cuts11922 : List PrefixCut := [⟨41,362760273,362760547⟩,
⟨89,778512029,778512622⟩,
⟨128,1117176591,1117177447⟩]
theorem checked11922 : checkPrefixCuts (2^48) 1566572545 9 Manual.Count131072.C011922.packed 128 cuts11922 = true := by
 decide +kernel
def pointBounds11922 : List (Nat × Nat × Nat) := [(1566614528,93239159317388,93239535187215),(1566663680,93239575069144,93239950939290)]
theorem point_links_checked11922 : (cuts11922.take 2).map (fun c => (1566572545-1+2*2^9*c.k,93238796557115+c.lower,93239172426668+c.upper)) = pointBounds11922 := by
 decide +kernel
def cuts11923 : List PrefixCut := [⟨9,78691105,78691165⟩,
⟨57,502680896,502681283⟩,
⟨105,924321910,924322624⟩,
⟨128,1122472478,1122473341⟩]
theorem checked11923 : checkPrefixCuts (2^48) 1566703617 9 Manual.Count131072.C011923.packed 128 cuts11923 = true := by
 decide +kernel
def pointBounds11923 : List (Nat × Nat × Nat) := [(1566712832,93239992424811,93240368295280),(1566761984,93240416414602,93240792285398),(1566811136,93240838055616,93241213926739)]
theorem point_links_checked11923 : (cuts11923.take 3).map (fun c => (1566703617-1+2*2^9*c.k,93239913733706+c.lower,93240289604115+c.upper)) = pointBounds11923 := by
 decide +kernel
def cuts11924 : List PrefixCut := [⟨25,215572902,215573067⟩,
⟨73,629462991,629463475⟩,
⟨121,1051782917,1051783728⟩,
⟨128,1112318541,1112319401⟩]
theorem checked11924 : checkPrefixCuts (2^48) 1566834689 9 Manual.Count131072.C011924.packed 128 cuts11924 = true := by
 decide +kernel
def pointBounds11924 : List (Nat × Nat × Nat) := [(1566860288,93241251779086,93241627650523),(1566909440,93241665669175,93242041540931),(1566958592,93242087989101,93242463861184)]
theorem point_links_checked11924 : (cuts11924.take 3).map (fun c => (1566834689-1+2*2^9*c.k,93241036206184+c.lower,93241412077456+c.upper)) = pointBounds11924 := by
 decide +kernel
def cuts11925 : List PrefixCut := [⟨41,340754556,340754819⟩,
⟨89,763766442,763767026⟩,
⟨128,1111506428,1111507279⟩]
theorem checked11925 : checkPrefixCuts (2^48) 1566965761 9 Manual.Count131072.C011925.packed 128 cuts11925 = true := by
 decide +kernel
def pointBounds11925 : List (Nat × Nat × Nat) := [(1567007744,93242489279281,93242865151676),(1567056896,93242912291167,93243288163883)]
theorem point_links_checked11925 : (cuts11925.take 2).map (fun c => (1566965761-1+2*2^9*c.k,93242148524725+c.lower,93242524396857+c.upper)) = pointBounds11925 := by
 decide +kernel
def cuts11926 : List PrefixCut := [⟨9,78850980,78851040⟩,
⟨57,505608236,505608622⟩,
⟨105,927502706,927503420⟩,
⟨128,1132069182,1132070053⟩]
theorem checked11926 : checkPrefixCuts (2^48) 1567096833 9 Manual.Count131072.C011926.packed 128 cuts11926 = true := by
 decide +kernel
def pointBounds11926 : List (Nat × Nat × Nat) := [(1567106048,93243338882133,93243714755176),(1567155200,93243765639389,93244141512758),(1567204352,93244187533859,93244563407556)]
theorem point_links_checked11926 : (cuts11926.take 3).map (fun c => (1567096833-1+2*2^9*c.k,93243260031153+c.lower,93243635904136+c.upper)) = pointBounds11926 := by
 decide +kernel
def cuts11927 : List PrefixCut := [⟨25,218751580,218751749⟩,
⟨73,625174505,625174990⟩,
⟨121,1039666136,1039666941⟩,
⟨128,1099109061,1099109913⟩]
theorem checked11927 : checkPrefixCuts (2^48) 1567227905 9 Manual.Count131072.C011927.packed 128 cuts11927 = true := by
 decide +kernel
def pointBounds11927 : List (Nat × Nat × Nat) := [(1567253504,93244610851915,93244986725938),(1567302656,93245017274840,93245393149179),(1567351808,93245431766471,93245807641130)]
theorem point_links_checked11927 : (cuts11927.take 3).map (fun c => (1567227905-1+2*2^9*c.k,93244392100335+c.lower,93244767974189+c.upper)) = pointBounds11927 := by
 decide +kernel
def cuts11928 : List PrefixCut := [⟨41,365451459,365451739⟩,
⟨89,802543861,802544478⟩,
⟨128,1140320222,1140321096⟩]
theorem checked11928 : checkPrefixCuts (2^48) 1567358977 9 Manual.Count131072.C011928.packed 128 cuts11928 = true := by
 decide +kernel
def pointBounds11928 : List (Nat × Nat × Nat) := [(1567400960,93245856660855,93246232535841),(1567450112,93246293753257,93246669628580)]
theorem point_links_checked11928 : (cuts11928.take 2).map (fun c => (1567358977-1+2*2^9*c.k,93245491209396+c.lower,93245867084102+c.upper)) = pointBounds11928 := by
 decide +kernel
def cuts11929 : List PrefixCut := [⟨9,80626891,80626953⟩,
⟨57,487704327,487704701⟩,
⟨105,905183468,905184159⟩,
⟨128,1104671015,1104671859⟩]
theorem checked11929 : checkPrefixCuts (2^48) 1567490049 9 Manual.Count131072.C011929.packed 128 cuts11929 = true := by
 decide +kernel
def pointBounds11929 : List (Nat × Nat × Nat) := [(1567499264,93246712156509,93247088032151),(1567548416,93247119233945,93247495109899),(1567597568,93247536713086,93247912589357)]
theorem point_links_checked11929 : (cuts11929.take 3).map (fun c => (1567490049-1+2*2^9*c.k,93246631529618+c.lower,93247007405198+c.upper)) = pointBounds11929 := by
 decide +kernel
def cuts11930 : List PrefixCut := [⟨25,217978502,217978672⟩,
⟨73,624299457,624299938⟩,
⟨121,1042098428,1042099229⟩,
⟨128,1104758167,1104759015⟩]
theorem checked11930 : checkPrefixCuts (2^48) 1567621121 9 Manual.Count131072.C011930.packed 128 cuts11930 = true := by
 decide +kernel
def pointBounds11930 : List (Nat × Nat × Nat) := [(1567646720,93247954179135,93248330055729),(1567695872,93248360500090,93248736376995),(1567745024,93248778299061,93249154176286)]
theorem point_links_checked11930 : (cuts11930.take 3).map (fun c => (1567621121-1+2*2^9*c.k,93247736200633+c.lower,93248112077057+c.upper)) = pointBounds11930 := by
 decide +kernel
def cuts11931 : List PrefixCut := [⟨41,353330831,353331100⟩,
⟨89,773976156,773976750⟩,
⟨128,1112924415,1112925266⟩]
theorem checked11931 : checkPrefixCuts (2^48) 1567752193 9 Manual.Count131072.C011931.packed 128 cuts11931 = true := by
 decide +kernel
def pointBounds11931 : List (Nat × Nat × Nat) := [(1567794176,93249194289631,93249570167172),(1567843328,93249614934956,93249990812822)]
theorem point_links_checked11931 : (cuts11931.take 2).map (fun c => (1567752193-1+2*2^9*c.k,93248840958800+c.lower,93249216836072+c.upper)) = pointBounds11931 := by
 decide +kernel
def cuts11932 : List PrefixCut := [⟨9,79170468,79170528⟩,
⟨57,482914390,482914760⟩,
⟨105,890415496,890416179⟩,
⟨128,1093263746,1093264582⟩]
theorem checked11932 : checkPrefixCuts (2^48) 1567883265 9 Manual.Count131072.C011932.packed 128 cuts11932 = true := by
 decide +kernel
def pointBounds11932 : List (Nat × Nat × Nat) := [(1567892480,93250033053683,93250408931866),(1567941632,93250436797605,93250812676098),(1567990784,93250844298711,93251220177517)]
theorem point_links_checked11932 : (cuts11932.take 3).map (fun c => (1567883265-1+2*2^9*c.k,93249953883215+c.lower,93250329761338+c.upper)) = pointBounds11932 := by
 decide +kernel
def cuts11933 : List PrefixCut := [⟨25,218103336,218103501⟩,
⟨73,638503153,638503647⟩,
⟨121,1053145776,1053146588⟩,
⟨128,1111840909,1111841765⟩]
theorem checked11933 : checkPrefixCuts (2^48) 1568014337 9 Manual.Count131072.C011933.packed 128 cuts11933 = true := by
 decide +kernel
def pointBounds11933 : List (Nat × Nat × Nat) := [(1568039936,93251265250297,93251641129421),(1568089088,93251685650114,93252061529567),(1568138240,93252100292737,93252476172508)]
theorem point_links_checked11933 : (cuts11933.take 3).map (fun c => (1568014337-1+2*2^9*c.k,93251047146961+c.lower,93251423025920+c.upper)) = pointBounds11933 := by
 decide +kernel
def cuts11934 : List PrefixCut := [⟨41,362575839,362576116⟩,
⟨89,764269493,764270080⟩,
⟨128,1106363421,1106364267⟩]
theorem checked11934 : checkPrefixCuts (2^48) 1568145409 9 Manual.Count131072.C011934.packed 128 cuts11934 = true := by
 decide +kernel
def pointBounds11934 : List (Nat × Nat × Nat) := [(1568187392,93252521563709,93252897443801),(1568236544,93252923257363,93253299137765)]
theorem point_links_checked11934 : (cuts11934.take 2).map (fun c => (1568145409-1+2*2^9*c.k,93252158987870+c.lower,93252534867685+c.upper)) = pointBounds11934 := by
 decide +kernel
def cuts11935 : List PrefixCut := [⟨9,80945426,80945488⟩,
⟨57,488536627,488537001⟩,
⟨105,904011652,904012347⟩,
⟨128,1104296536,1104297384⟩]
theorem checked11935 : checkPrefixCuts (2^48) 1568276481 9 Manual.Count131072.C011935.packed 128 cuts11935 = true := by
 decide +kernel
def pointBounds11935 : List (Nat × Nat × Nat) := [(1568285696,93253346296717,93253722177440),(1568334848,93253753887918,93254129768953),(1568384000,93254169362943,93254545244299)]
theorem point_links_checked11935 : (cuts11935.take 3).map (fun c => (1568276481-1+2*2^9*c.k,93253265351291+c.lower,93253641231952+c.upper)) = pointBounds11935 := by
 decide +kernel
def cuts11936 : List PrefixCut := [⟨25,224509397,224509570⟩,
⟨73,638343354,638343844⟩,
⟨121,1052523276,1052524082⟩,
⟨128,1111383136,1111383990⟩]
theorem checked11936 : checkPrefixCuts (2^48) 1568407553 9 Manual.Count131072.C011936.packed 128 cuts11936 = true := by
 decide +kernel
def pointBounds11936 : List (Nat × Nat × Nat) := [(1568433152,93254594157224,93254970038906),(1568482304,93255007991181,93255383873180),(1568531456,93255422171103,93255798053418)]
theorem point_links_checked11936 : (cuts11936.take 3).map (fun c => (1568407553-1+2*2^9*c.k,93254369647827+c.lower,93254745529336+c.upper)) = pointBounds11936 := by
 decide +kernel
def cuts11937 : List PrefixCut := [⟨41,359793277,359793554⟩,
⟨89,783816610,783817218⟩,
⟨128,1116673479,1116674343⟩]
theorem checked11937 : checkPrefixCuts (2^48) 1568538625 9 Manual.Count131072.C011937.packed 128 cuts11937 = true := by
 decide +kernel
def pointBounds11937 : List (Nat × Nat × Nat) := [(1568580608,93255840824240,93256216706880),(1568629760,93256264847573,93256640730544)]
theorem point_links_checked11937 : (cuts11937.take 2).map (fun c => (1568538625-1+2*2^9*c.k,93255481030963+c.lower,93255856913326+c.upper)) = pointBounds11937 := by
 decide +kernel
def cuts11938 : List PrefixCut := [⟨9,77336443,77336501⟩,
⟨57,496488435,496488815⟩,
⟨105,917421594,917422295⟩,
⟨128,1113350154,1113351007⟩]
theorem checked11938 : checkPrefixCuts (2^48) 1568669697 9 Manual.Count131072.C011938.packed 128 cuts11938 = true := by
 decide +kernel
def pointBounds11938 : List (Nat × Nat × Nat) := [(1568678912,93256675040885,93257050924170),(1568728064,93257094192877,93257470076484),(1568777216,93257515126036,93257891009964)]
theorem point_links_checked11938 : (cuts11938.take 3).map (fun c => (1568669697-1+2*2^9*c.k,93256597704442+c.lower,93256973587669+c.upper)) = pointBounds11938 := by
 decide +kernel
def cuts11939 : List PrefixCut := [⟨25,212073132,212073295⟩,
⟨73,624547457,624547936⟩,
⟨121,1046338094,1046338898⟩,
⟨128,1103030331,1103031180⟩]
theorem checked11939 : checkPrefixCuts (2^48) 1568800769 9 Manual.Count131072.C011939.packed 128 cuts11939 = true := by
 decide +kernel
def pointBounds11939 : List (Nat × Nat × Nat) := [(1568826368,93257923127728,93258299011971),(1568875520,93258335602053,93258711486612),(1568924672,93258757392690,93259133277574)]
theorem point_links_checked11939 : (cuts11939.take 3).map (fun c => (1568800769-1+2*2^9*c.k,93257711054596+c.lower,93258086938676+c.upper)) = pointBounds11939 := by
 decide +kernel
def cuts11940 : List PrefixCut := [⟨41,354859198,354859470⟩,
⟨89,768371047,768371642⟩,
⟨128,1112625637,1112626497⟩]
theorem checked11940 : checkPrefixCuts (2^48) 1568931841 9 Manual.Count131072.C011940.packed 128 cuts11940 = true := by
 decide +kernel
def pointBounds11940 : List (Nat × Nat × Nat) := [(1568973824,93259168944125,93259544829326),(1569022976,93259582455974,93259958341498)]
theorem point_links_checked11940 : (cuts11940.take 2).map (fun c => (1568931841-1+2*2^9*c.k,93258814084927+c.lower,93259189969856+c.upper)) = pointBounds11940 := by
 decide +kernel
def cuts11941 : List PrefixCut := [⟨9,76061324,76061380⟩,
⟨57,497799150,497799532⟩,
⟨105,912348463,912349161⟩,
⟨128,1107869154,1107870004⟩]
theorem checked11941 : checkPrefixCuts (2^48) 1569062913 9 Manual.Count131072.C011941.packed 128 cuts11941 = true := by
 decide +kernel
def pointBounds11941 : List (Nat × Nat × Nat) := [(1569072128,93260002771888,93260378657733),(1569121280,93260424509714,93260800395885),(1569170432,93260839059027,93261214945514)]
theorem point_links_checked11941 : (cuts11941.take 3).map (fun c => (1569062913-1+2*2^9*c.k,93259926710564+c.lower,93260302596353+c.upper)) = pointBounds11941 := by
 decide +kernel
def cuts11942 : List PrefixCut := [⟨25,212916900,212917066⟩,
⟨73,621700554,621701032⟩,
⟨121,1045896612,1045897414⟩,
⟨128,1107417389,1107418238⟩]
theorem checked11942 : checkPrefixCuts (2^48) 1569193985 9 Manual.Count131072.C011942.packed 128 cuts11942 = true := by
 decide +kernel
def pointBounds11942 : List (Nat × Nat × Nat) := [(1569219584,93261247496618,93261623383423),(1569268736,93261656280272,93262032167389),(1569317888,93262080476330,93262456363771)]
theorem point_links_checked11942 : (cuts11942.take 3).map (fun c => (1569193985-1+2*2^9*c.k,93261034579718+c.lower,93261410466357+c.upper)) = pointBounds11942 := by
 decide +kernel
def cuts11943 : List PrefixCut := [⟨41,353694150,353694423⟩,
⟨89,774994002,774994596⟩,
⟨128,1116651479,1116652334⟩]
theorem checked11943 : checkPrefixCuts (2^48) 1569325057 9 Manual.Count131072.C011943.packed 128 cuts11943 = true := by
 decide +kernel
def pointBounds11943 : List (Nat × Nat × Nat) := [(1569367040,93262495691257,93262871579018),(1569416192,93262916991109,93263292879191)]
theorem point_links_checked11943 : (cuts11943.take 2).map (fun c => (1569325057-1+2*2^9*c.k,93262141997107+c.lower,93262517884595+c.upper)) = pointBounds11943 := by
 decide +kernel
def cuts11944 : List PrefixCut := [⟨9,78553090,78553153⟩,
⟨57,495163680,495164061⟩,
⟨105,917320628,917321331⟩,
⟨128,1116558293,1116559152⟩]
theorem checked11944 : checkPrefixCuts (2^48) 1569456129 9 Manual.Count131072.C011944.packed 128 cuts11944 = true := by
 decide +kernel
def pointBounds11944 : List (Nat × Nat × Nat) := [(1569465344,93263337201676,93263713090082),(1569514496,93263753812266,93264129700990),(1569563648,93264175969214,93264551858260)]
theorem point_links_checked11944 : (cuts11944.take 3).map (fun c => (1569456129-1+2*2^9*c.k,93263258648586+c.lower,93263634536929+c.upper)) = pointBounds11944 := by
 decide +kernel
def cuts11945 : List PrefixCut := [⟨25,215194862,215195025⟩,
⟨73,635352758,635353247⟩,
⟨121,1051193792,1051194601⟩,
⟨128,1109650789,1109651644⟩]
theorem checked11945 : checkPrefixCuts (2^48) 1569587201 9 Manual.Count131072.C011945.packed 128 cuts11945 = true := by
 decide +kernel
def pointBounds11945 : List (Nat × Nat × Nat) := [(1569612800,93264590401741,93264966291106),(1569661952,93265010559637,93265386449328),(1569711104,93265426400671,93265802290682)]
theorem point_links_checked11945 : (cuts11945.take 3).map (fun c => (1569587201-1+2*2^9*c.k,93264375206879+c.lower,93264751096081+c.upper)) = pointBounds11945 := by
 decide +kernel
def cuts11946 : List PrefixCut := [⟨41,358805515,358805787⟩,
⟨89,762427634,762428217⟩,
⟨128,1100772072,1100772916⟩]
theorem checked11946 : checkPrefixCuts (2^48) 1569718273 9 Manual.Count131072.C011946.packed 128 cuts11946 = true := by
 decide +kernel
def pointBounds11946 : List (Nat × Nat × Nat) := [(1569760256,93265843663183,93266219553512),(1569809408,93266247285302,93266623175942)]
theorem point_links_checked11946 : (cuts11946.take 2).map (fun c => (1569718273-1+2*2^9*c.k,93265484857668+c.lower,93265860747725+c.upper)) = pointBounds11946 := by
 decide +kernel
def cuts11947 : List PrefixCut := [⟨9,76561113,76561174⟩,
⟨57,503108040,503108425⟩,
⟨105,919601326,919602028⟩,
⟨128,1126677761,1126678622⟩]
theorem checked11947 : checkPrefixCuts (2^48) 1569849345 9 Manual.Count131072.C011947.packed 128 cuts11947 = true := by
 decide +kernel
def pointBounds11947 : List (Nat × Nat × Nat) := [(1569858560,93266662190853,93267038081815),(1569907712,93267088737780,93267464629066),(1569956864,93267505231066,93267881122669)]
theorem point_links_checked11947 : (cuts11947.take 3).map (fun c => (1569849345-1+2*2^9*c.k,93266585629740+c.lower,93266961520641+c.upper)) = pointBounds11947 := by
 decide +kernel
def cuts11948 : List PrefixCut := [⟨25,212810247,212810408⟩,
⟨73,626408911,626409393⟩,
⟨121,1042325193,1042325994⟩,
⟨128,1098078488,1098079332⟩]
theorem checked11948 : checkPrefixCuts (2^48) 1569980417 9 Manual.Count131072.C011948.packed 128 cuts11948 = true := by
 decide +kernel
def pointBounds11948 : List (Nat × Nat × Nat) := [(1570006016,93267925117748,93268301009671),(1570055168,93268338716412,93268714608656),(1570104320,93268754632694,93269130525257)]
theorem point_links_checked11948 : (cuts11948.take 3).map (fun c => (1569980417-1+2*2^9*c.k,93267712307501+c.lower,93268088199263+c.upper)) = pointBounds11948 := by
 decide +kernel
def cuts11949 : List PrefixCut := [⟨41,364273014,364273290⟩,
⟨89,780880338,780880932⟩,
⟨128,1112866044,1112866893⟩]
theorem checked11949 : checkPrefixCuts (2^48) 1570111489 9 Manual.Count131072.C011949.packed 128 cuts11949 = true := by
 decide +kernel
def pointBounds11949 : List (Nat × Nat × Nat) := [(1570153472,93269174659003,93269550551885),(1570202624,93269591266327,93269967159527)]
theorem point_links_checked11949 : (cuts11949.take 2).map (fun c => (1570111489-1+2*2^9*c.k,93268810385989+c.lower,93269186278595+c.upper)) = pointBounds11949 := by
 decide +kernel
def cuts11950 : List PrefixCut := [⟨9,84070658,84070724⟩,
⟨57,500472539,500472925⟩,
⟨105,914889738,914890443⟩,
⟨128,1116895524,1116896387⟩]
theorem checked11950 : checkPrefixCuts (2^48) 1570242561 9 Manual.Count131072.C011950.packed 128 cuts11950 = true := by
 decide +kernel
def pointBounds11950 : List (Nat × Nat × Nat) := [(1570251776,93270007322691,93270383216212),(1570300928,93270423724572,93270799618413),(1570350080,93270838141771,93271214035931)]
theorem point_links_checked11950 : (cuts11950.take 3).map (fun c => (1570242561-1+2*2^9*c.k,93269923252033+c.lower,93270299145488+c.upper)) = pointBounds11950 := by
 decide +kernel
def cuts11951 : List PrefixCut := [⟨25,218851106,218851275⟩,
⟨73,635572430,635572919⟩,
⟨121,1046545184,1046545990⟩,
⟨128,1107661304,1107662158⟩]
theorem checked11951 : checkPrefixCuts (2^48) 1570373633 9 Manual.Count131072.C011951.packed 128 cuts11951 = true := by
 decide +kernel
def pointBounds11951 : List (Nat × Nat × Nat) := [(1570399232,93271258998663,93271634893150),(1570448384,93271675719987,93272051614794),(1570497536,93272086692741,93272462587865)]
theorem point_links_checked11951 : (cuts11951.take 3).map (fun c => (1570373633-1+2*2^9*c.k,93271040147557+c.lower,93271416041875+c.upper)) = pointBounds11951 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000060
