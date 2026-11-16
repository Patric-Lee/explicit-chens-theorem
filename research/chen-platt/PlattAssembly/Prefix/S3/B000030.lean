import PlattAssemblyKernel
import PlattCertificates.Count131072.C020960
import PlattCertificates.Count131072.C020961
import PlattCertificates.Count131072.C020962
import PlattCertificates.Count131072.C020963
import PlattCertificates.Count131072.C020964
import PlattCertificates.Count131072.C020965
import PlattCertificates.Count131072.C020966
import PlattCertificates.Count131072.C020967
import PlattCertificates.Count131072.C020968
import PlattCertificates.Count131072.C020969
import PlattCertificates.Count131072.C020970
import PlattCertificates.Count131072.C020971
import PlattCertificates.Count131072.C020972
import PlattCertificates.Count131072.C020973
import PlattCertificates.Count131072.C020974
import PlattCertificates.Count131072.C020975
import PlattCertificates.Count131072.C020976
import PlattCertificates.Count131072.C020977
import PlattCertificates.Count131072.C020978
import PlattCertificates.Count131072.C020979
import PlattCertificates.Count131072.C020980
import PlattCertificates.Count131072.C020981
import PlattCertificates.Count131072.C020982
import PlattCertificates.Count131072.C020983
import PlattCertificates.Count131072.C020984
import PlattCertificates.Count131072.C020985
import PlattCertificates.Count131072.C020986
import PlattCertificates.Count131072.C020987
import PlattCertificates.Count131072.C020988
import PlattCertificates.Count131072.C020989
import PlattCertificates.Count131072.C020990
import PlattCertificates.Count131072.C020991
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000030
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts20960 : List PrefixCut := [⟨81,395830733,395830956⟩,
⟨128,619880525,619880879⟩]
theorem checked20960 : checkPrefixCuts (2^48) 2751201281 9 Manual.Count131072.C020960.packed 128 cuts20960 = true := by
 decide +kernel
def pointBounds20960 : List (Nat × Nat × Nat) := [(2751284224,100628058338500,100628439062673)]
theorem point_links_checked20960 : (cuts20960.take 1).map (fun c => (2751201281-1+2*2^9*c.k,100627662507767+c.lower,100628043231717+c.upper)) = pointBounds20960 := by
 decide +kernel
def cuts20961 : List PrefixCut := [⟨37,180464666,180464770⟩,
⟨121,590797679,590798016⟩,
⟨128,623840643,623841000⟩]
theorem checked20961 : checkPrefixCuts (2^48) 2751332353 9 Manual.Count131072.C020961.packed 128 cuts20961 = true := by
 decide +kernel
def pointBounds20961 : List (Nat × Nat × Nat) := [(2751370240,100628462852958,100628843577366),(2751456256,100628873185971,100629253910612)]
theorem point_links_checked20961 : (cuts20961.take 2).map (fun c => (2751332353-1+2*2^9*c.k,100628282388292+c.lower,100628663112596+c.upper)) = pointBounds20961 := by
 decide +kernel
def cuts20962 : List PrefixCut := [⟨77,371037023,371037232⟩,
⟨128,617570811,617571164⟩]
theorem checked20962 : checkPrefixCuts (2^48) 2751463425 9 Manual.Count131072.C020962.packed 128 cuts20962 = true := by
 decide +kernel
def pointBounds20962 : List (Nat × Nat × Nat) := [(2751542272,100629277265958,100629657990828)]
theorem point_links_checked20962 : (cuts20962.take 1).map (fun c => (2751463425-1+2*2^9*c.k,100628906228935+c.lower,100629286953596+c.upper)) = pointBounds20962 := by
 decide +kernel
def cuts20963 : List PrefixCut := [⟨33,157738228,157738320⟩,
⟨117,561588432,561588759⟩,
⟨128,612222244,612222603⟩]
theorem checked20963 : checkPrefixCuts (2^48) 2751594497 9 Manual.Count131072.C020963.packed 128 cuts20963 = true := by
 decide +kernel
def pointBounds20963 : List (Nat × Nat × Nat) := [(2751628288,100629681537974,100630062263080),(2751714304,100630085388178,100630466113519)]
theorem point_links_checked20963 : (cuts20963.take 2).map (fun c => (2751594497-1+2*2^9*c.k,100629523799746+c.lower,100629904524760+c.upper)) = pointBounds20963 := by
 decide +kernel
def cuts20964 : List PrefixCut := [⟨73,340008467,340008668⟩,
⟨128,604419069,604419421⟩]
theorem checked20964 : checkPrefixCuts (2^48) 2751725569 9 Manual.Count131072.C020964.packed 128 cuts20964 = true := by
 decide +kernel
def pointBounds20964 : List (Nat × Nat × Nat) := [(2751800320,100630476030457,100630856756031)]
theorem point_links_checked20964 : (cuts20964.take 1).map (fun c => (2751725569-1+2*2^9*c.k,100630136021990+c.lower,100630516747363+c.upper)) = pointBounds20964 := by
 decide +kernel
def cuts20965 : List PrefixCut := [⟨29,145551413,145551495⟩,
⟨113,548647721,548648037⟩,
⟨128,621164851,621165206⟩]
theorem checked20965 : checkPrefixCuts (2^48) 2751856641 9 Manual.Count131072.C020965.packed 128 cuts20965 = true := by
 decide +kernel
def pointBounds20965 : List (Nat × Nat × Nat) := [(2751886336,100630885992472,100631266718279),(2751972352,100631289088780,100631669814821)]
theorem point_links_checked20965 : (cuts20965.take 2).map (fun c => (2751856641-1+2*2^9*c.k,100630740441059+c.lower,100631121166784+c.upper)) = pointBounds20965 := by
 decide +kernel
def cuts20966 : List PrefixCut := [⟨69,329952924,329953113⟩,
⟨128,612441530,612441883⟩]
theorem checked20966 : checkPrefixCuts (2^48) 2751987713 9 Manual.Count131072.C020966.packed 128 cuts20966 = true := by
 decide +kernel
def pointBounds20966 : List (Nat × Nat × Nat) := [(2752058368,100631691558834,100632072285103)]
theorem point_links_checked20966 : (cuts20966.take 1).map (fun c => (2751987713-1+2*2^9*c.k,100631361605910+c.lower,100631742331990+c.upper)) = pointBounds20966 := by
 decide +kernel
def cuts20967 : List PrefixCut := [⟨25,124162131,124162200⟩,
⟨109,525277407,525277707⟩,
⟨128,616401046,616401397⟩]
theorem checked20967 : checkPrefixCuts (2^48) 2752118785 9 Manual.Count131072.C020967.packed 128 cuts20967 = true := by
 decide +kernel
def pointBounds20967 : List (Nat × Nat × Nat) := [(2752144384,100632098209571,100632478936073),(2752230400,100632499324847,100632880051580)]
theorem point_links_checked20967 : (cuts20967.take 2).map (fun c => (2752118785-1+2*2^9*c.k,100631974047440+c.lower,100632354773873+c.upper)) = pointBounds20967 := by
 decide +kernel
def cuts20968 : List PrefixCut := [⟨65,317649350,317649533⟩,
⟨128,622098707,622099065⟩]
theorem checked20968 : checkPrefixCuts (2^48) 2752249857 9 Manual.Count131072.C020968.packed 128 cuts20968 = true := by
 decide +kernel
def pointBounds20968 : List (Nat × Nat × Nat) := [(2752316416,100632908097836,100633288824803)]
theorem point_links_checked20968 : (cuts20968.take 1).map (fun c => (2752249857-1+2*2^9*c.k,100632590448486+c.lower,100632971175270+c.upper)) = pointBounds20968 := by
 decide +kernel
def cuts20969 : List PrefixCut := [⟨21,102674642,102674702⟩,
⟨105,506922536,506922834⟩,
⟨128,615319751,615320115⟩]
theorem checked20969 : checkPrefixCuts (2^48) 2752380929 9 Manual.Count131072.C020969.packed 128 cuts20969 = true := by
 decide +kernel
def pointBounds20969 : List (Nat × Nat × Nat) := [(2752402432,100633315221835,100633695949037),(2752488448,100633719469729,100634100197169)]
theorem point_links_checked20969 : (cuts20969.take 2).map (fun c => (2752380929-1+2*2^9*c.k,100633212547193+c.lower,100633593274335+c.upper)) = pointBounds20969 := by
 decide +kernel
def cuts20970 : List PrefixCut := [⟨61,297576405,297576580⟩,
⟨128,623062022,623062386⟩]
theorem checked20970 : checkPrefixCuts (2^48) 2752512001 9 Manual.Count131072.C020970.packed 128 cuts20970 = true := by
 decide +kernel
def pointBounds20970 : List (Nat × Nat × Nat) := [(2752574464,100634125443349,100634506171030)]
theorem point_links_checked20970 : (cuts20970.take 1).map (fun c => (2752512001-1+2*2^9*c.k,100633827866944+c.lower,100634208594450+c.upper)) = pointBounds20970 := by
 decide +kernel
def cuts20971 : List PrefixCut := [⟨18,84667877,84667927⟩,
⟨103,497262559,497262837⟩,
⟨128,619657999,619658348⟩]
theorem checked20971 : checkPrefixCuts (2^48) 2752643073 9 Manual.Count131072.C020971.packed 128 cuts20971 = true := by
 decide +kernel
def pointBounds20971 : List (Nat × Nat × Nat) := [(2752661504,100634535596843,100634916324763),(2752748544,100634948191525,100635328919673)]
theorem point_links_checked20971 : (cuts20971.take 2).map (fun c => (2752643073-1+2*2^9*c.k,100634450928966+c.lower,100634831656836+c.upper)) = pointBounds20971 := by
 decide +kernel
def cuts20972 : List PrefixCut := [⟨60,285584853,285585014⟩,
⟨128,616560960,616561306⟩]
theorem checked20972 : checkPrefixCuts (2^48) 2752774145 9 Manual.Count131072.C020972.packed 128 cuts20972 = true := by
 decide +kernel
def pointBounds20972 : List (Nat × Nat × Nat) := [(2752835584,100635356171818,100635736900198)]
theorem point_links_checked20972 : (cuts20972.take 1).map (fun c => (2752774145-1+2*2^9*c.k,100635070586965+c.lower,100635451315184+c.upper)) = pointBounds20972 := by
 decide +kernel
def cuts20973 : List PrefixCut := [⟨17,84864318,84864367⟩,
⟨102,492409818,492410103⟩,
⟨128,613771228,613771581⟩]
theorem checked20973 : checkPrefixCuts (2^48) 2752905217 9 Manual.Count131072.C020973.packed 128 cuts20973 = true := by
 decide +kernel
def pointBounds20973 : List (Nat × Nat × Nat) := [(2752922624,100635772012243,100636152740857),(2753009664,100636179557743,100636560286593)]
theorem point_links_checked20973 : (cuts20973.take 2).map (fun c => (2752905217-1+2*2^9*c.k,100635687147925+c.lower,100636067876490+c.upper)) = pointBounds20973 := by
 decide +kernel
def cuts20974 : List PrefixCut := [⟨59,281877075,281877235⟩,
⟨128,612208215,612208567⟩]
theorem checked20974 : checkPrefixCuts (2^48) 2753036289 9 Manual.Count131072.C020974.packed 128 cuts20974 = true := by
 decide +kernel
def pointBounds20974 : List (Nat × Nat × Nat) := [(2753096704,100636582796228,100636963525306)]
theorem point_links_checked20974 : (cuts20974.take 1).map (fun c => (2753036289-1+2*2^9*c.k,100636300919153+c.lower,100636681648071+c.upper)) = pointBounds20974 := by
 decide +kernel
def cuts20975 : List PrefixCut := [⟨16,79437721,79437767⟩,
⟨101,480299366,480299650⟩,
⟨128,609725581,609725942⟩]
theorem checked20975 : checkPrefixCuts (2^48) 2753167361 9 Manual.Count131072.C020975.packed 128 cuts20975 = true := by
 decide +kernel
def pointBounds20975 : List (Nat × Nat × Nat) := [(2753183744,100636992565089,100637373294405),(2753270784,100637393426734,100637774156288)]
theorem point_links_checked20975 : (cuts20975.take 2).map (fun c => (2753167361-1+2*2^9*c.k,100636913127368+c.lower,100637293856638+c.upper)) = pointBounds20975 := by
 decide +kernel
def cuts20976 : List PrefixCut := [⟨58,277249916,277250073⟩,
⟨128,619408225,619408576⟩]
theorem checked20976 : checkPrefixCuts (2^48) 2753298433 9 Manual.Count131072.C020976.packed 128 cuts20976 = true := by
 decide +kernel
def pointBounds20976 : List (Nat × Nat × Nat) := [(2753357824,100637800102865,100638180832653)]
theorem point_links_checked20976 : (cuts20976.take 1).map (fun c => (2753298433-1+2*2^9*c.k,100637522852949+c.lower,100637903582580+c.upper)) = pointBounds20976 := by
 decide +kernel
def cuts20977 : List PrefixCut := [⟨15,70638678,70638719⟩,
⟨100,484751468,484751750⟩,
⟨128,621627622,621627983⟩]
theorem checked20977 : checkPrefixCuts (2^48) 2753429505 9 Manual.Count131072.C020977.packed 128 cuts20977 = true := by
 decide +kernel
def pointBounds20977 : List (Nat × Nat × Nat) := [(2753444864,100638212899852,100638593629875),(2753531904,100638627012642,100639007742906)]
theorem point_links_checked20977 : (cuts20977.take 2).map (fun c => (2753429505-1+2*2^9*c.k,100638142261174+c.lower,100638522991156+c.upper)) = pointBounds20977 := by
 decide +kernel
def cuts20978 : List PrefixCut := [⟨57,274668020,274668177⟩,
⟨128,618735970,618736326⟩]
theorem checked20978 : checkPrefixCuts (2^48) 2753560577 9 Manual.Count131072.C020978.packed 128 cuts20978 = true := by
 decide +kernel
def pointBounds20978 : List (Nat × Nat × Nat) := [(2753618944,100639038556816,100639419287316)]
theorem point_links_checked20978 : (cuts20978.take 1).map (fun c => (2753560577-1+2*2^9*c.k,100638763888796+c.lower,100639144619139+c.upper)) = pointBounds20978 := by
 decide +kernel
def cuts20979 : List PrefixCut := [⟨14,65316674,65316710⟩,
⟨99,465897848,465898114⟩,
⟨128,608076097,608076444⟩]
theorem checked20979 : checkPrefixCuts (2^48) 2753691649 9 Manual.Count131072.C020979.packed 128 cuts20979 = true := by
 decide +kernel
def pointBounds20979 : List (Nat × Nat × Nat) := [(2753705984,100639447941440,100639828672175),(2753793024,100639848522614,100640229253579)]
theorem point_links_checked20979 : (cuts20979.take 2).map (fun c => (2753691649-1+2*2^9*c.k,100639382624766+c.lower,100639763355465+c.upper)) = pointBounds20979 := by
 decide +kernel
def cuts20980 : List PrefixCut := [⟨56,268918085,268918236⟩,
⟨128,613362159,613362508⟩]
theorem checked20980 : checkPrefixCuts (2^48) 2753822721 9 Manual.Count131072.C020980.packed 128 cuts20980 = true := by
 decide +kernel
def pointBounds20980 : List (Nat × Nat × Nat) := [(2753880064,100640259618948,100640640350145)]
theorem point_links_checked20980 : (cuts20980.take 1).map (fun c => (2753822721-1+2*2^9*c.k,100639990700863+c.lower,100640371431909+c.upper)) = pointBounds20980 := by
 decide +kernel
def cuts20981 : List PrefixCut := [⟨13,60608934,60608972⟩,
⟨98,471985864,471986138⟩,
⟨128,610266889,610267246⟩]
theorem checked20981 : checkPrefixCuts (2^48) 2753953793 9 Manual.Count131072.C020981.packed 128 cuts20981 = true := by
 decide +kernel
def pointBounds20981 : List (Nat × Nat × Nat) := [(2753967104,100640664671956,100641045403389),(2754054144,100641076048886,100641456780555)]
theorem point_links_checked20981 : (cuts20981.take 2).map (fun c => (2753953793-1+2*2^9*c.k,100640604063022+c.lower,100640984794417+c.upper)) = pointBounds20981 := by
 decide +kernel
def cuts20982 : List PrefixCut := [⟨55,264395689,264395839⟩,
⟨128,610135588,610135945⟩]
theorem checked20982 : checkPrefixCuts (2^48) 2754084865 9 Manual.Count131072.C020982.packed 128 cuts20982 = true := by
 decide +kernel
def pointBounds20982 : List (Nat × Nat × Nat) := [(2754141184,100641478725600,100641859457502)]
theorem point_links_checked20982 : (cuts20982.take 1).map (fun c => (2754084865-1+2*2^9*c.k,100641214329911+c.lower,100641595061663+c.upper)) = pointBounds20982 := by
 decide +kernel
def cuts20983 : List PrefixCut := [⟨12,57843845,57843878⟩,
⟨97,467751026,467751297⟩,
⟨128,614500971,614501329⟩]
theorem checked20983 : checkPrefixCuts (2^48) 2754215937 9 Manual.Count131072.C020983.packed 128 cuts20983 = true := by
 decide +kernel
def pointBounds20983 : List (Nat × Nat × Nat) := [(2754228224,100641882309344,100642263041486),(2754315264,100642292216525,100642672948905)]
theorem point_links_checked20983 : (cuts20983.take 2).map (fun c => (2754215937-1+2*2^9*c.k,100641824465499+c.lower,100642205197608+c.upper)) = pointBounds20983 := by
 decide +kernel
def cuts20984 : List PrefixCut := [⟨54,261407006,261407157⟩,
⟨128,624997267,624997626⟩]
theorem checked20984 : checkPrefixCuts (2^48) 2754347009 9 Manual.Count131072.C020984.packed 128 cuts20984 = true := by
 decide +kernel
def pointBounds20984 : List (Nat × Nat × Nat) := [(2754402304,100642700373476,100643081106094)]
theorem point_links_checked20984 : (cuts20984.take 1).map (fun c => (2754347009-1+2*2^9*c.k,100642438966470+c.lower,100642819698937+c.upper)) = pointBounds20984 := by
 decide +kernel
def cuts20985 : List PrefixCut := [⟨11,52013637,52013667⟩,
⟨96,460042633,460042894⟩,
⟨128,616383915,616384263⟩]
theorem checked20985 : checkPrefixCuts (2^48) 2754478081 9 Manual.Count131072.C020985.packed 128 cuts20985 = true := by
 decide +kernel
def pointBounds20985 : List (Nat × Nat × Nat) := [(2754489344,100643115977374,100643496710230),(2754576384,100643524006370,100643904739457)]
theorem point_links_checked20985 : (cuts20985.take 2).map (fun c => (2754478081-1+2*2^9*c.k,100643063963737+c.lower,100643444696563+c.upper)) = pointBounds20985 := by
 decide +kernel
def cuts20986 : List PrefixCut := [⟨53,254433776,254433921⟩,
⟨128,619011339,619011693⟩]
theorem checked20986 : checkPrefixCuts (2^48) 2754609153 9 Manual.Count131072.C020986.packed 128 cuts20986 = true := by
 decide +kernel
def pointBounds20986 : List (Nat × Nat × Nat) := [(2754663424,100643934781428,100644315514747)]
theorem point_links_checked20986 : (cuts20986.take 1).map (fun c => (2754609153-1+2*2^9*c.k,100643680347652+c.lower,100644061080826+c.upper)) = pointBounds20986 := by
 decide +kernel
def cuts20987 : List PrefixCut := [⟨10,49760778,49760806⟩,
⟨95,455605359,455605623⟩,
⟨128,614997028,614997383⟩]
theorem checked20987 : checkPrefixCuts (2^48) 2754740225 9 Manual.Count131072.C020987.packed 128 cuts20987 = true := by
 decide +kernel
def pointBounds20987 : List (Nat × Nat × Nat) := [(2754750464,100644349119769,100644729853325),(2754837504,100644754964350,100645135698142)]
theorem point_links_checked20987 : (cuts20987.take 2).map (fun c => (2754740225-1+2*2^9*c.k,100644299358991+c.lower,100644680092519+c.upper)) = pointBounds20987 := by
 decide +kernel
def cuts20988 : List PrefixCut := [⟨52,247564026,247564172⟩,
⟨128,614661161,614661520⟩]
theorem checked20988 : checkPrefixCuts (2^48) 2754871297 9 Manual.Count131072.C020988.packed 128 cuts20988 = true := by
 decide +kernel
def pointBounds20988 : List (Nat × Nat × Nat) := [(2754924544,100645161920045,100645542654074)]
theorem point_links_checked20988 : (cuts20988.take 1).map (fun c => (2754871297-1+2*2^9*c.k,100644914356019+c.lower,100645295089902+c.upper)) = pointBounds20988 := by
 decide +kernel
def cuts20989 : List PrefixCut := [⟨9,44851965,44851990⟩,
⟨94,451884130,451884387⟩,
⟨128,616266741,616267091⟩]
theorem checked20989 : checkPrefixCuts (2^48) 2755002369 9 Manual.Count131072.C020989.packed 128 cuts20989 = true := by
 decide +kernel
def pointBounds20989 : List (Nat × Nat × Nat) := [(2755011584,100645573869145,100645954603412),(2755098624,100645980901310,100646361635809)]
theorem point_links_checked20989 : (cuts20989.take 2).map (fun c => (2755002369-1+2*2^9*c.k,100645529017180+c.lower,100645909751422+c.upper)) = pointBounds20989 := by
 decide +kernel
def cuts20990 : List PrefixCut := [⟨51,246416750,246416894⟩,
⟨128,616135228,616135589⟩]
theorem checked20990 : checkPrefixCuts (2^48) 2755133441 9 Manual.Count131072.C020990.packed 128 cuts20990 = true := by
 decide +kernel
def pointBounds20990 : List (Nat × Nat × Nat) := [(2755185664,100646391700671,100646772435407)]
theorem point_links_checked20990 : (cuts20990.take 1).map (fun c => (2755133441-1+2*2^9*c.k,100646145283921+c.lower,100646526018513+c.upper)) = pointBounds20990 := by
 decide +kernel
def cuts20991 : List PrefixCut := [⟨8,38718177,38718201⟩,
⟨93,444690223,444690479⟩,
⟨128,613756329,613756689⟩]
theorem checked20991 : checkPrefixCuts (2^48) 2755264513 9 Manual.Count131072.C020991.packed 128 cuts20991 = true := by
 decide +kernel
def pointBounds20991 : List (Nat × Nat × Nat) := [(2755272704,100646800137326,100647180872303),(2755359744,100647206109372,100647586844581)]
theorem point_links_checked20991 : (cuts20991.take 2).map (fun c => (2755264513-1+2*2^9*c.k,100646761419149+c.lower,100647142154102+c.upper)) = pointBounds20991 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000030
