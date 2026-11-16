import PlattAssemblyKernel
import PlattCertificates.Count131072.C018000
import PlattCertificates.Count131072.C018001
import PlattCertificates.Count131072.C018002
import PlattCertificates.Count131072.C018003
import PlattCertificates.Count131072.C018004
import PlattCertificates.Count131072.C018005
import PlattCertificates.Count131072.C018006
import PlattCertificates.Count131072.C018007
import PlattCertificates.Count131072.C018008
import PlattCertificates.Count131072.C018009
import PlattCertificates.Count131072.C018010
import PlattCertificates.Count131072.C018011
import PlattCertificates.Count131072.C018012
import PlattCertificates.Count131072.C018013
import PlattCertificates.Count131072.C018014
import PlattCertificates.Count131072.C018015
import PlattCertificates.Count131072.C018016
import PlattCertificates.Count131072.C018017
import PlattCertificates.Count131072.C018018
import PlattCertificates.Count131072.C018019
import PlattCertificates.Count131072.C018020
import PlattCertificates.Count131072.C018021
import PlattCertificates.Count131072.C018022
import PlattCertificates.Count131072.C018023
import PlattCertificates.Count131072.C018024
import PlattCertificates.Count131072.C018025
import PlattCertificates.Count131072.C018026
import PlattCertificates.Count131072.C018027
import PlattCertificates.Count131072.C018028
import PlattCertificates.Count131072.C018029
import PlattCertificates.Count131072.C018030
import PlattCertificates.Count131072.C018031
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000250
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts18000 : List PrefixCut := [⟨32,181635544,181635654⟩,
⟨105,601352970,601353335⟩,
⟨128,735578768,735579215⟩]
theorem checked18000 : checkPrefixCuts (2^48) 2363228161 9 Manual.Count131072.C018000.packed 128 cuts18000 = true := by
 decide +kernel
def pointBounds18000 : List (Nat × Nat × Nat) := [(2363260928,98652413856716,98652793407338),(2363335680,98652833574142,98653213125019)]
theorem point_links_checked18000 : (cuts18000.take 2).map (fun c => (2363228161-1+2*2^9*c.k,98652232221172+c.lower,98652611771684+c.upper)) = pointBounds18000 := by
 decide +kernel
def cuts18001 : List PrefixCut := [⟨50,288694046,288694224⟩,
⟨123,692068964,692069390⟩,
⟨128,720532195,720532638⟩]
theorem checked18001 : checkPrefixCuts (2^48) 2363359233 9 Manual.Count131072.C018001.packed 128 cuts18001 = true := by
 decide +kernel
def pointBounds18001 : List (Nat × Nat × Nat) := [(2363410432,98653256493986,98653636045123),(2363485184,98653659868904,98654039420289)]
theorem point_links_checked18001 : (cuts18001.take 2).map (fun c => (2363359233-1+2*2^9*c.k,98652967799940+c.lower,98653347350899+c.upper)) = pointBounds18001 := by
 decide +kernel
def cuts18002 : List PrefixCut := [⟨68,376923406,376923638⟩,
⟨128,723230778,723231218⟩]
theorem checked18002 : checkPrefixCuts (2^48) 2363490305 9 Manual.Count131072.C018002.packed 128 cuts18002 = true := by
 decide +kernel
def pointBounds18002 : List (Nat × Nat × Nat) := [(2363559936,98654065255541,98654444807175)]
theorem point_links_checked18002 : (cuts18002.take 1).map (fun c => (2363490305-1+2*2^9*c.k,98653688332135+c.lower,98654067883537+c.upper)) = pointBounds18002 := by
 decide +kernel
def cuts18003 : List PrefixCut := [⟨13,73476034,73476079⟩,
⟨86,488363727,488364031⟩,
⟨128,726644362,726644811⟩]
theorem checked18003 : checkPrefixCuts (2^48) 2363621377 9 Manual.Count131072.C018003.packed 128 cuts18003 = true := by
 decide +kernel
def pointBounds18003 : List (Nat × Nat × Nat) := [(2363634688,98654485038947,98654864590834),(2363709440,98654899926640,98655279478786)]
theorem point_links_checked18003 : (cuts18003.take 2).map (fun c => (2363621377-1+2*2^9*c.k,98654411562913+c.lower,98654791114755+c.upper)) = pointBounds18003 := by
 decide +kernel
def cuts18004 : List PrefixCut := [⟨31,174569668,174569774⟩,
⟨104,586097013,586097370⟩,
⟨128,725651393,725651836⟩]
theorem checked18004 : checkPrefixCuts (2^48) 2363752449 9 Manual.Count131072.C018004.packed 128 cuts18004 = true := by
 decide +kernel
def pointBounds18004 : List (Nat × Nat × Nat) := [(2363784192,98655312776943,98655692329340),(2363858944,98655724304288,98656103856936)]
theorem point_links_checked18004 : (cuts18004.take 2).map (fun c => (2363752449-1+2*2^9*c.k,98655138207275+c.lower,98655517759566+c.upper)) = pointBounds18004 := by
 decide +kernel
def cuts18005 : List PrefixCut := [⟨49,271483744,271483915⟩,
⟨122,681675320,681675746⟩,
⟨128,715609309,715609755⟩]
theorem checked18005 : checkPrefixCuts (2^48) 2363883521 9 Manual.Count131072.C018005.packed 128 cuts18005 = true := by
 decide +kernel
def pointBounds18005 : List (Nat × Nat × Nat) := [(2363933696,98656135342412,98656514895317),(2364008448,98656545533988,98656925087148)]
theorem point_links_checked18005 : (cuts18005.take 2).map (fun c => (2363883521-1+2*2^9*c.k,98655863858668+c.lower,98656243411402+c.upper)) = pointBounds18005 := by
 decide +kernel
def cuts18006 : List PrefixCut := [⟨67,374696746,374696978⟩,
⟨128,716284063,716284500⟩]
theorem checked18006 : checkPrefixCuts (2^48) 2364014593 9 Manual.Count131072.C018006.packed 128 cuts18006 = true := by
 decide +kernel
def pointBounds18006 : List (Nat × Nat × Nat) := [(2364083200,98656954164723,98657333718135)]
theorem point_links_checked18006 : (cuts18006.take 1).map (fun c => (2364014593-1+2*2^9*c.k,98656579467977+c.lower,98656959021157+c.upper)) = pointBounds18006 := by
 decide +kernel
def cuts18007 : List PrefixCut := [⟨12,66435244,66435284⟩,
⟨85,475754550,475754844⟩,
⟨128,713625220,713625661⟩]
theorem checked18007 : checkPrefixCuts (2^48) 2364145665 9 Manual.Count131072.C018007.packed 128 cuts18007 = true := by
 decide +kernel
def pointBounds18007 : List (Nat × Nat × Nat) := [(2364157952,98657362187284,98657741740941),(2364232704,98657771506590,98658151060501)]
theorem point_links_checked18007 : (cuts18007.take 2).map (fun c => (2364145665-1+2*2^9*c.k,98657295752040+c.lower,98657675305657+c.upper)) = pointBounds18007 := by
 decide +kernel
def cuts18008 : List PrefixCut := [⟨30,169530778,169530885⟩,
⟨103,581086124,581086482⟩,
⟨128,721323869,721324314⟩]
theorem checked18008 : checkPrefixCuts (2^48) 2364276737 9 Manual.Count131072.C018008.packed 128 cuts18008 = true := by
 decide +kernel
def pointBounds18008 : List (Nat × Nat × Nat) := [(2364307456,98658178908038,98658558462203),(2364382208,98658590463384,98658970017800)]
theorem point_links_checked18008 : (cuts18008.take 2).map (fun c => (2364276737-1+2*2^9*c.k,98658009377260+c.lower,98658388931318+c.upper)) = pointBounds18008 := by
 decide +kernel
def cuts18009 : List PrefixCut := [⟨48,269161727,269161896⟩,
⟨121,681048195,681048612⟩,
⟨128,724497888,724498330⟩]
theorem checked18009 : checkPrefixCuts (2^48) 2364407809 9 Manual.Count131072.C018009.packed 128 cuts18009 = true := by
 decide +kernel
def pointBounds18009 : List (Nat × Nat × Nat) := [(2364456960,98658999862856,98659379417528),(2364531712,98659411749324,98659791304244)]
theorem point_links_checked18009 : (cuts18009.take 2).map (fun c => (2364407809-1+2*2^9*c.k,98658730701129+c.lower,98659110255632+c.upper)) = pointBounds18009 := by
 decide +kernel
def cuts18010 : List PrefixCut := [⟨66,374018634,374018866⟩,
⟨128,725172098,725172546⟩]
theorem checked18010 : checkPrefixCuts (2^48) 2364538881 9 Manual.Count131072.C018010.packed 128 cuts18010 = true := by
 decide +kernel
def pointBounds18010 : List (Nat × Nat × Nat) := [(2364606464,98659829217651,98660208772828)]
theorem point_links_checked18010 : (cuts18010.take 1).map (fun c => (2364538881-1+2*2^9*c.k,98659455199017+c.lower,98659834753962+c.upper)) = pointBounds18010 := by
 decide +kernel
def cuts18011 : List PrefixCut := [⟨11,61659192,61659231⟩,
⟨84,472197230,472197520⟩,
⟨128,724179552,724179993⟩]
theorem checked18011 : checkPrefixCuts (2^48) 2364669953 9 Manual.Count131072.C018011.packed 128 cuts18011 = true := by
 decide +kernel
def pointBounds18011 : List (Nat × Nat × Nat) := [(2364681216,98660242030307,98660621585739),(2364755968,98660652568345,98661032124028)]
theorem point_links_checked18011 : (cuts18011.take 2).map (fun c => (2364669953-1+2*2^9*c.k,98660180371115+c.lower,98660559926508+c.upper)) = pointBounds18011 := by
 decide +kernel
def cuts18012 : List PrefixCut := [⟨29,167707825,167707924⟩,
⟨102,579053021,579053370⟩,
⟨128,722116210,722116651⟩]
theorem checked18012 : checkPrefixCuts (2^48) 2364801025 9 Manual.Count131072.C018012.packed 128 cuts18012 = true := by
 decide +kernel
def pointBounds18012 : List (Nat × Nat × Nat) := [(2364830720,98661072258492,98661451814425),(2364905472,98661483603688,98661863159871)]
theorem point_links_checked18012 : (cuts18012.take 2).map (fun c => (2364801025-1+2*2^9*c.k,98660904550667+c.lower,98661284106501+c.upper)) = pointBounds18012 := by
 decide +kernel
def cuts18013 : List PrefixCut := [⟨47,270054274,270054438⟩,
⟨120,677922047,677922459⟩,
⟨128,721957189,721957629⟩]
theorem checked18013 : checkPrefixCuts (2^48) 2364932097 9 Manual.Count131072.C018013.packed 128 cuts18013 = true := by
 decide +kernel
def pointBounds18013 : List (Nat × Nat × Nat) := [(2364980224,98661896721151,98662276277590),(2365054976,98662304588924,98662684145611)]
theorem point_links_checked18013 : (cuts18013.take 2).map (fun c => (2364932097-1+2*2^9*c.k,98661626666877+c.lower,98662006223152+c.upper)) = pointBounds18013 := by
 decide +kernel
def cuts18014 : List PrefixCut := [⟨65,366318976,366319206⟩,
⟨128,729176569,729177020⟩]
theorem checked18014 : checkPrefixCuts (2^48) 2365063169 9 Manual.Count131072.C018014.packed 128 cuts18014 = true := by
 decide +kernel
def pointBounds18014 : List (Nat × Nat × Nat) := [(2365129728,98662714943042,98663094499987)]
theorem point_links_checked18014 : (cuts18014.take 1).map (fun c => (2365063169-1+2*2^9*c.k,98662348624066+c.lower,98662728180781+c.upper)) = pointBounds18014 := by
 decide +kernel
def cuts18015 : List PrefixCut := [⟨10,54386124,54386157⟩,
⟨83,460430139,460430425⟩,
⟨128,714260688,714261132⟩]
theorem checked18015 : checkPrefixCuts (2^48) 2365194241 9 Manual.Count131072.C018015.packed 128 cuts18015 = true := by
 decide +kernel
def pointBounds18015 : List (Nat × Nat × Nat) := [(2365204480,98663132186759,98663511743958),(2365279232,98663538230774,98663917788226)]
theorem point_links_checked18015 : (cuts18015.take 2).map (fun c => (2365194241-1+2*2^9*c.k,98663077800635+c.lower,98663457357801+c.upper)) = pointBounds18015 := by
 decide +kernel
def cuts18016 : List PrefixCut := [⟨28,163981695,163981791⟩,
⟨101,576901979,576902330⟩,
⟨128,726716193,726716638⟩]
theorem checked18016 : checkPrefixCuts (2^48) 2365325313 9 Manual.Count131072.C018016.packed 128 cuts18016 = true := by
 decide +kernel
def pointBounds18016 : List (Nat × Nat × Nat) := [(2365353984,98663956043018,98664335600724),(2365428736,98664368963302,98664748521263)]
theorem point_links_checked18016 : (cuts18016.take 2).map (fun c => (2365325313-1+2*2^9*c.k,98663792061323+c.lower,98664171618933+c.upper)) = pointBounds18016 := by
 decide +kernel
def cuts18017 : List PrefixCut := [⟨46,258214201,258214358⟩,
⟨119,670632365,670632773⟩,
⟨128,722748909,722749349⟩]
theorem checked18017 : checkPrefixCuts (2^48) 2365456385 9 Manual.Count131072.C018017.packed 128 cuts18017 = true := by
 decide +kernel
def pointBounds18017 : List (Nat × Nat × Nat) := [(2365503488,98664776991717,98665156549929),(2365578240,98665189409881,98665568968344)]
theorem point_links_checked18017 : (cuts18017.take 2).map (fun c => (2365456385-1+2*2^9*c.k,98664518777516+c.lower,98664898335571+c.upper)) = pointBounds18017 := by
 decide +kernel
def cuts18018 : List PrefixCut := [⟨64,362549298,362549522⟩,
⟨128,714618093,714618539⟩]
theorem checked18018 : checkPrefixCuts (2^48) 2365587457 9 Manual.Count131072.C018018.packed 128 cuts18018 = true := by
 decide +kernel
def pointBounds18018 : List (Nat × Nat × Nat) := [(2365652992,98665604075723,98665983634442)]
theorem point_links_checked18018 : (cuts18018.take 1).map (fun c => (2365587457-1+2*2^9*c.k,98665241526425+c.lower,98665621084920+c.upper)) = pointBounds18018 := by
 decide +kernel
def cuts18019 : List PrefixCut := [⟨9,48544037,48544067⟩,
⟨82,461993883,461994164⟩,
⟨128,720051311,720051753⟩]
theorem checked18019 : checkPrefixCuts (2^48) 2365718529 9 Manual.Count131072.C018019.packed 128 cuts18019 = true := by
 decide +kernel
def pointBounds18019 : List (Nat × Nat × Nat) := [(2365727744,98666004688555,98666384247526),(2365802496,98666418138401,98666797697623)]
theorem point_links_checked18019 : (cuts18019.take 2).map (fun c => (2365718529-1+2*2^9*c.k,98665956144518+c.lower,98666335703459+c.upper)) = pointBounds18019 := by
 decide +kernel
def cuts18020 : List PrefixCut := [⟨27,155855174,155855269⟩,
⟨100,567256430,567256775⟩,
⟨128,725365251,725365691⟩]
theorem checked18020 : checkPrefixCuts (2^48) 2365849601 9 Manual.Count131072.C018020.packed 128 cuts18020 = true := by
 decide +kernel
def pointBounds18020 : List (Nat × Nat × Nat) := [(2365877248,98666832051003,98667211610481),(2365952000,98667243452259,98667623011987)]
theorem point_links_checked18020 : (cuts18020.take 2).map (fun c => (2365849601-1+2*2^9*c.k,98666676195829+c.lower,98667055755212+c.upper)) = pointBounds18020 := by
 decide +kernel
def cuts18021 : List PrefixCut := [⟨45,250067283,250067437⟩,
⟨118,667152764,667153169⟩,
⟨128,724016216,724016657⟩]
theorem checked18021 : checkPrefixCuts (2^48) 2365980673 9 Manual.Count131072.C018021.packed 128 cuts18021 = true := by
 decide +kernel
def pointBounds18021 : List (Nat × Nat × Nat) := [(2366026752,98667651628363,98668031188340),(2366101504,98668068713844,98668448274072)]
theorem point_links_checked18021 : (cuts18021.take 2).map (fun c => (2365980673-1+2*2^9*c.k,98667401561080+c.lower,98667781120903+c.upper)) = pointBounds18021 := by
 decide +kernel
def cuts18022 : List PrefixCut := [⟨63,351048977,351049189⟩,
⟨128,715411392,715411827⟩]
theorem checked18022 : checkPrefixCuts (2^48) 2366111745 9 Manual.Count131072.C018022.packed 128 cuts18022 = true := by
 decide +kernel
def pointBounds18022 : List (Nat × Nat × Nat) := [(2366176256,98668476626273,98668856186749)]
theorem point_links_checked18022 : (cuts18022.take 1).map (fun c => (2366111745-1+2*2^9*c.k,98668125577296+c.lower,98668505137560+c.upper)) = pointBounds18022 := by
 decide +kernel
def cuts18023 : List PrefixCut := [⟨8,49009109,49009139⟩,
⟨81,462129619,462129900⟩,
⟨128,729289030,729289473⟩]
theorem checked18023 : checkPrefixCuts (2^48) 2366242817 9 Manual.Count131072.C018023.packed 128 cuts18023 = true := by
 decide +kernel
def pointBounds18023 : List (Nat × Nat × Nat) := [(2366251008,98668889997797,98669269558526),(2366325760,98669303118307,98669682679287)]
theorem point_links_checked18023 : (cuts18023.take 2).map (fun c => (2366242817-1+2*2^9*c.k,98668840988688+c.lower,98669220549387+c.upper)) = pointBounds18023 := by
 decide +kernel
def cuts18024 : List PrefixCut := [⟨26,148564912,148565001⟩,
⟨99,556544665,556545007⟩,
⟨128,724847494,724847937⟩]
theorem checked18024 : checkPrefixCuts (2^48) 2366373889 9 Manual.Count131072.C018024.packed 128 cuts18024 = true := by
 decide +kernel
def pointBounds18024 : List (Nat × Nat × Nat) := [(2366400512,98669718842630,98670098403861),(2366475264,98670126822383,98670506383867)]
theorem point_links_checked18024 : (cuts18024.take 2).map (fun c => (2366373889-1+2*2^9*c.k,98669570277718+c.lower,98669949838860+c.upper)) = pointBounds18024 := by
 decide +kernel
def cuts18025 : List PrefixCut := [⟨44,250487735,250487887⟩,
⟨117,657133424,657133820⟩,
⟨128,717314473,717314903⟩]
theorem checked18025 : checkPrefixCuts (2^48) 2366504961 9 Manual.Count131072.C018025.packed 128 cuts18025 = true := by
 decide +kernel
def pointBounds18025 : List (Nat × Nat × Nat) := [(2366550016,98670545612947,98670925174684),(2366624768,98670952258636,98671331820617)]
theorem point_links_checked18025 : (cuts18025.take 2).map (fun c => (2366504961-1+2*2^9*c.k,98670295125212+c.lower,98670674686797+c.upper)) = pointBounds18025 := by
 decide +kernel
def cuts18026 : List PrefixCut := [⟨62,350138703,350138923⟩,
⟨128,720604763,720605205⟩]
theorem checked18026 : checkPrefixCuts (2^48) 2366636033 9 Manual.Count131072.C018026.packed 128 cuts18026 = true := by
 decide +kernel
def pointBounds18026 : List (Nat × Nat × Nat) := [(2366699520,98671362578388,98671742140623)]
theorem point_links_checked18026 : (cuts18026.take 1).map (fun c => (2366636033-1+2*2^9*c.k,98671012439685+c.lower,98671392001700+c.upper)) = pointBounds18026 := by
 decide +kernel
def cuts18027 : List PrefixCut := [⟨7,39959751,39959773⟩,
⟨80,451680736,451681012⟩,
⟨128,724846073,724846515⟩]
theorem checked18027 : checkPrefixCuts (2^48) 2366767105 9 Manual.Count131072.C018027.packed 128 cuts18027 = true := by
 decide +kernel
def pointBounds18027 : List (Nat × Nat × Nat) := [(2366774272,98671773004199,98672152566678),(2366849024,98672184725184,98672564287917)]
theorem point_links_checked18027 : (cuts18027.take 2).map (fun c => (2366767105-1+2*2^9*c.k,98671733044448+c.lower,98672112606905+c.upper)) = pointBounds18027 := by
 decide +kernel
def cuts18028 : List PrefixCut := [⟨25,141277889,141277974⟩,
⟨98,558799884,558800218⟩,
⟨128,730751853,730752287⟩]
theorem checked18028 : checkPrefixCuts (2^48) 2366898177 9 Manual.Count131072.C018028.packed 128 cuts18028 = true := by
 decide +kernel
def pointBounds18028 : List (Nat × Nat × Nat) := [(2366923776,98672599168410,98672978731394),(2366998528,98673016690405,98673396253638)]
theorem point_links_checked18028 : (cuts18028.take 2).map (fun c => (2366898177-1+2*2^9*c.k,98672457890521+c.lower,98672837453420+c.upper)) = pointBounds18028 := by
 decide +kernel
def cuts18029 : List PrefixCut := [⟨43,245913584,245913733⟩,
⟨116,659366247,659366650⟩,
⟨128,724528139,724528581⟩]
theorem checked18029 : checkPrefixCuts (2^48) 2367029249 9 Manual.Count131072.C018029.packed 128 cuts18029 = true := by
 decide +kernel
def pointBounds18029 : List (Nat × Nat × Nat) := [(2367073280,98673434555958,98673814119440),(2367148032,98673848008621,98674227572357)]
theorem point_links_checked18029 : (cuts18029.take 2).map (fun c => (2367029249-1+2*2^9*c.k,98673188642374+c.lower,98673568205707+c.upper)) = pointBounds18029 := by
 decide +kernel
def cuts18030 : List PrefixCut := [⟨61,344829400,344829609⟩,
⟨128,724131266,724131711⟩]
theorem checked18030 : checkPrefixCuts (2^48) 2367160321 9 Manual.Count131072.C018030.packed 128 cuts18030 = true := by
 decide +kernel
def pointBounds18030 : List (Nat × Nat × Nat) := [(2367222784,98674257999913,98674637563897)]
theorem point_links_checked18030 : (cuts18030.take 1).map (fun c => (2367160321-1+2*2^9*c.k,98673913170513+c.lower,98674292734288+c.upper)) = pointBounds18030 := by
 decide +kernel
def cuts18031 : List PrefixCut := [⟨6,31746703,31746722⟩,
⟨79,444090113,444090388⟩,
⟨128,719216226,719216669⟩]
theorem checked18031 : checkPrefixCuts (2^48) 2367291393 9 Manual.Count131072.C018031.packed 128 cuts18031 = true := by
 decide +kernel
def pointBounds18031 : List (Nat × Nat × Nat) := [(2367297536,98674669048482,98675048612721),(2367372288,98675081391892,98675460956387)]
theorem point_links_checked18031 : (cuts18031.take 2).map (fun c => (2367291393-1+2*2^9*c.k,98674637301779+c.lower,98675016865999+c.upper)) = pointBounds18031 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000250
