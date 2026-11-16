import PlattAssemblyKernel
import PlattCertificates.Count131072.C013776
import PlattCertificates.Count131072.C013777
import PlattCertificates.Count131072.C013778
import PlattCertificates.Count131072.C013779
import PlattCertificates.Count131072.C013780
import PlattCertificates.Count131072.C013781
import PlattCertificates.Count131072.C013782
import PlattCertificates.Count131072.C013783
import PlattCertificates.Count131072.C013784
import PlattCertificates.Count131072.C013785
import PlattCertificates.Count131072.C013786
import PlattCertificates.Count131072.C013787
import PlattCertificates.Count131072.C013788
import PlattCertificates.Count131072.C013789
import PlattCertificates.Count131072.C013790
import PlattCertificates.Count131072.C013791
import PlattCertificates.Count131072.C013792
import PlattCertificates.Count131072.C013793
import PlattCertificates.Count131072.C013794
import PlattCertificates.Count131072.C013795
import PlattCertificates.Count131072.C013796
import PlattCertificates.Count131072.C013797
import PlattCertificates.Count131072.C013798
import PlattCertificates.Count131072.C013799
import PlattCertificates.Count131072.C013800
import PlattCertificates.Count131072.C013801
import PlattCertificates.Count131072.C013802
import PlattCertificates.Count131072.C013803
import PlattCertificates.Count131072.C013804
import PlattCertificates.Count131072.C013805
import PlattCertificates.Count131072.C013806
import PlattCertificates.Count131072.C013807
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000118
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts13776 : List PrefixCut := [⟨35,261005356,261005538⟩,
⟨91,677078919,677079387⟩,
⟨128,950980326,950980989⟩]
theorem checked13776 : checkPrefixCuts (2^48) 1809580033 9 Manual.Count131072.C013776.packed 128 cuts13776 = true := by
 decide +kernel
def pointBounds13776 : List (Nat × Nat × Nat) := [(1809615872,95149787453616,95150164723882),(1809673216,95150203527179,95150580797731)]
theorem point_links_checked13776 : (cuts13776.take 2).map (fun c => (1809580033-1+2*2^9*c.k,95149526448260+c.lower,95149903718344+c.upper)) = pointBounds13776 := by
 decide +kernel
def cuts13777 : List PrefixCut := [⟨19,143869845,143869944⟩,
⟨75,566293786,566294181⟩,
⟨128,946245938,946246601⟩]
theorem checked13777 : checkPrefixCuts (2^48) 1809711105 9 Manual.Count131072.C013777.packed 128 cuts13777 = true := by
 decide +kernel
def pointBounds13777 : List (Nat × Nat × Nat) := [(1809730560,95150621298431,95150998569277),(1809787904,95151043722372,95151420993514)]
theorem point_links_checked13777 : (cuts13777.take 2).map (fun c => (1809711105-1+2*2^9*c.k,95150477428586+c.lower,95150854699333+c.upper)) = pointBounds13777 := by
 decide +kernel
def cuts13778 : List PrefixCut := [⟨3,22551040,22551055⟩,
⟨59,441371297,441371605⟩,
⟨115,857067938,857068539⟩,
⟨128,956130263,956130933⟩]
theorem checked13778 : checkPrefixCuts (2^48) 1809842177 9 Manual.Count131072.C013778.packed 128 cuts13778 = true := by
 decide +kernel
def pointBounds13778 : List (Nat × Nat × Nat) := [(1809845248,95151446225564,95151823496989),(1809902592,95151865045821,95152242317539),(1809959936,95152280742462,95152658014473)]
theorem point_links_checked13778 : (cuts13778.take 3).map (fun c => (1809842177-1+2*2^9*c.k,95151423674524+c.lower,95151800945934+c.upper)) = pointBounds13778 := by
 decide +kernel
def cuts13779 : List PrefixCut := [⟨43,321908569,321908796⟩,
⟨99,745354169,745354690⟩,
⟨128,960570717,960571390⟩]
theorem checked13779 : checkPrefixCuts (2^48) 1809973249 9 Manual.Count131072.C013779.packed 128 cuts13779 = true := by
 decide +kernel
def pointBounds13779 : List (Nat × Nat × Nat) := [(1810017280,95152701713356,95153078985663),(1810074624,95153125158956,95153502431557)]
theorem point_links_checked13779 : (cuts13779.take 2).map (fun c => (1809973249-1+2*2^9*c.k,95152379804787+c.lower,95152757076867+c.upper)) = pointBounds13779 := by
 decide +kernel
def cuts13780 : List PrefixCut := [⟨27,207904662,207904807⟩,
⟨83,623704128,623704563⟩,
⟨128,954437163,954437829⟩]
theorem checked13780 : checkPrefixCuts (2^48) 1810104321 9 Manual.Count131072.C013780.packed 128 cuts13780 = true := by
 decide +kernel
def pointBounds13780 : List (Nat × Nat × Nat) := [(1810131968,95153548280166,95153925553064),(1810189312,95153964079632,95154341352820)]
theorem point_links_checked13780 : (cuts13780.take 2).map (fun c => (1810104321-1+2*2^9*c.k,95153340375504+c.lower,95153717648257+c.upper)) = pointBounds13780 := by
 decide +kernel
def cuts13781 : List PrefixCut := [⟨11,82409847,82409906⟩,
⟨67,503158559,503158914⟩,
⟨123,920317861,920318506⟩,
⟨128,956389156,956389826⟩]
theorem checked13781 : checkPrefixCuts (2^48) 1810235393 9 Manual.Count131072.C013781.packed 128 cuts13781 = true := by
 decide +kernel
def pointBounds13781 : List (Nat × Nat × Nat) := [(1810246656,95154377222514,95154754495992),(1810304000,95154797971226,95155175245000),(1810361344,95155215130528,95155592404592)]
theorem point_links_checked13781 : (cuts13781.take 3).map (fun c => (1810235393-1+2*2^9*c.k,95154294812667+c.lower,95154672086086+c.upper)) = pointBounds13781 := by
 decide +kernel
def cuts13782 : List PrefixCut := [⟨51,378276156,378276421⟩,
⟨107,799762292,799762851⟩,
⟨128,961294778,961295450⟩]
theorem checked13782 : checkPrefixCuts (2^48) 1810366465 9 Manual.Count131072.C013782.packed 128 cuts13782 = true := by
 decide +kernel
def pointBounds13782 : List (Nat × Nat × Nat) := [(1810418688,95155629477979,95156006752333),(1810476032,95156050964115,95156428238763)]
theorem point_links_checked13782 : (cuts13782.take 2).map (fun c => (1810366465-1+2*2^9*c.k,95155251201823+c.lower,95155628475912+c.upper)) = pointBounds13782 := by
 decide +kernel
def cuts13783 : List PrefixCut := [⟨35,265692584,265692772⟩,
⟨91,683576303,683576782⟩,
⟨128,962935416,962936091⟩]
theorem checked13783 : checkPrefixCuts (2^48) 1810497537 9 Manual.Count131072.C013783.packed 128 cuts13783 = true := by
 decide +kernel
def pointBounds13783 : List (Nat × Nat × Nat) := [(1810533376,95156478189185,95156855464134),(1810590720,95156896072904,95157273348144)]
theorem point_links_checked13783 : (cuts13783.take 2).map (fun c => (1810497537-1+2*2^9*c.k,95156212496601+c.lower,95156589771362+c.upper)) = pointBounds13783 := by
 decide +kernel
def cuts13784 : List PrefixCut := [⟨19,140532370,140532469⟩,
⟨75,554037005,554037397⟩,
⟨128,953072186,953072857⟩]
theorem checked13784 : checkPrefixCuts (2^48) 1810628609 9 Manual.Count131072.C013784.packed 128 cuts13784 = true := by
 decide +kernel
def pointBounds13784 : List (Nat × Nat × Nat) := [(1810648064,95157315964387,95157693239922),(1810705408,95157729469022,95158106744850)]
theorem point_links_checked13784 : (cuts13784.take 2).map (fun c => (1810628609-1+2*2^9*c.k,95157175432017+c.lower,95157552707453+c.upper)) = pointBounds13784 := by
 decide +kernel
def cuts13785 : List PrefixCut := [⟨3,23938624,23938642⟩,
⟨59,433841931,433842236⟩,
⟨115,843265883,843266480⟩,
⟨128,940879110,940879775⟩]
theorem checked13785 : checkPrefixCuts (2^48) 1810759681 9 Manual.Count131072.C013785.packed 128 cuts13785 = true := by
 decide +kernel
def pointBounds13785 : List (Nat × Nat × Nat) := [(1810762752,95158152442827,95158529718952),(1810820096,95158562346134,95158939622546),(1810877440,95158971770086,95159349046790)]
theorem point_links_checked13785 : (cuts13785.take 3).map (fun c => (1810759681-1+2*2^9*c.k,95158128504203+c.lower,95158505780310+c.upper)) = pointBounds13785 := by
 decide +kernel
def cuts13786 : List PrefixCut := [⟨43,314284795,314285017⟩,
⟨99,730677161,730677673⟩,
⟨128,949359459,949360123⟩]
theorem checked13786 : checkPrefixCuts (2^48) 1810890753 9 Manual.Count131072.C013786.packed 128 cuts13786 = true := by
 decide +kernel
def pointBounds13786 : List (Nat × Nat × Nat) := [(1810934784,95159383668108,95159760945102),(1810992128,95159800060474,95160177337758)]
theorem point_links_checked13786 : (cuts13786.take 2).map (fun c => (1810890753-1+2*2^9*c.k,95159069383313+c.lower,95159446660085+c.upper)) = pointBounds13786 := by
 decide +kernel
def cuts13787 : List PrefixCut := [⟨27,200649905,200650043⟩,
⟨83,624631365,624631801⟩,
⟨128,949135764,949136426⟩]
theorem checked13787 : checkPrefixCuts (2^48) 1811021825 9 Manual.Count131072.C013787.packed 128 cuts13787 = true := by
 decide +kernel
def pointBounds13787 : List (Nat × Nat × Nat) := [(1811049472,95160219392677,95160596670251),(1811106816,95160643374137,95161020652009)]
theorem point_links_checked13787 : (cuts13787.take 2).map (fun c => (1811021825-1+2*2^9*c.k,95160018742772+c.lower,95160396020208+c.upper)) = pointBounds13787 := by
 decide +kernel
def cuts13788 : List PrefixCut := [⟨11,79415281,79415336⟩,
⟨67,494822342,494822686⟩,
⟨123,911148705,911149343⟩,
⟨128,948134133,948134797⟩]
theorem checked13788 : checkPrefixCuts (2^48) 1811152897 9 Manual.Count131072.C013788.packed 128 cuts13788 = true := by
 decide +kernel
def pointBounds13788 : List (Nat × Nat × Nat) := [(1811164160,95161047293817,95161424571970),(1811221504,95161462700878,95161839979320),(1811278848,95161879027241,95162256305977)]
theorem point_links_checked13788 : (cuts13788.take 3).map (fun c => (1811152897-1+2*2^9*c.k,95160967878536+c.lower,95161345156634+c.upper)) = pointBounds13788 := by
 decide +kernel
def cuts13789 : List PrefixCut := [⟨51,383678933,383679205⟩,
⟨107,800911311,800911871⟩,
⟨128,961584983,961585655⟩]
theorem checked13789 : checkPrefixCuts (2^48) 1811283969 9 Manual.Count131072.C013789.packed 128 cuts13789 = true := by
 decide +kernel
def pointBounds13789 : List (Nat × Nat × Nat) := [(1811336192,95162299691602,95162676970636),(1811393536,95162716923980,95163094203302)]
theorem point_links_checked13789 : (cuts13789.take 2).map (fun c => (1811283969-1+2*2^9*c.k,95161916012669+c.lower,95162293291431+c.upper)) = pointBounds13789 := by
 decide +kernel
def cuts13790 : List PrefixCut := [⟨35,267267308,267267490⟩,
⟨91,686027142,686027614⟩,
⟨128,966177050,966177716⟩]
theorem checked13790 : checkPrefixCuts (2^48) 1811415041 9 Manual.Count131072.C013790.packed 128 cuts13790 = true := by
 decide +kernel
def pointBounds13790 : List (Nat × Nat × Nat) := [(1811450880,95163144864960,95163522144576),(1811508224,95163563624794,95163940904700)]
theorem point_links_checked13790 : (cuts13790.take 2).map (fun c => (1811415041-1+2*2^9*c.k,95162877597652+c.lower,95163254877086+c.upper)) = pointBounds13790 := by
 decide +kernel
def cuts13791 : List PrefixCut := [⟨19,139373572,139373670⟩,
⟨75,556086909,556087296⟩,
⟨128,951035768,951036431⟩]
theorem checked13791 : checkPrefixCuts (2^48) 1811546113 9 Manual.Count131072.C013791.packed 128 cuts13791 = true := by
 decide +kernel
def pointBounds13791 : List (Nat × Nat × Nat) := [(1811565568,95163983148274,95164360428472),(1811622912,95164399861611,95164777142098)]
theorem point_links_checked13791 : (cuts13791.take 2).map (fun c => (1811546113-1+2*2^9*c.k,95163843774702+c.lower,95164221054802+c.upper)) = pointBounds13791 := by
 decide +kernel
def cuts13792 : List PrefixCut := [⟨3,21906730,21906746⟩,
⟨59,435641789,435642090⟩,
⟨115,845013755,845014342⟩,
⟨128,940402560,940403213⟩]
theorem checked13792 : checkPrefixCuts (2^48) 1811677185 9 Manual.Count131072.C013792.packed 128 cuts13792 = true := by
 decide +kernel
def pointBounds13792 : List (Nat × Nat × Nat) := [(1811680256,95164816717200,95165193997979),(1811737600,95165230452259,95165607733323),(1811794944,95165639824225,95166017105575)]
theorem point_links_checked13792 : (cuts13792.take 3).map (fun c => (1811677185-1+2*2^9*c.k,95164794810470+c.lower,95165172091233+c.upper)) = pointBounds13792 := by
 decide +kernel
def cuts13793 : List PrefixCut := [⟨43,319407593,319407818⟩,
⟨99,745376093,745376620⟩,
⟨128,958355196,958355874⟩]
theorem checked13793 : checkPrefixCuts (2^48) 1811808257 9 Manual.Count131072.C013793.packed 128 cuts13793 = true := by
 decide +kernel
def pointBounds13793 : List (Nat × Nat × Nat) := [(1811852288,95166054620623,95166431902264),(1811909632,95166480589123,95166857871066)]
theorem point_links_checked13793 : (cuts13793.take 2).map (fun c => (1811808257-1+2*2^9*c.k,95165735213030+c.lower,95166112494446+c.upper)) = pointBounds13793 := by
 decide +kernel
def cuts13794 : List PrefixCut := [⟨27,198839522,198839662⟩,
⟨83,623227570,623228003⟩,
⟨128,964654539,964655208⟩]
theorem checked13794 : checkPrefixCuts (2^48) 1811939329 9 Manual.Count131072.C013794.packed 128 cuts13794 = true := by
 decide +kernel
def pointBounds13794 : List (Nat × Nat × Nat) := [(1811966976,95166892407748,95167269689982),(1812024320,95167316795796,95167694078323)]
theorem point_links_checked13794 : (cuts13794.take 2).map (fun c => (1811939329-1+2*2^9*c.k,95166693568226+c.lower,95167070850320+c.upper)) = pointBounds13794 := by
 decide +kernel
def cuts13795 : List PrefixCut := [⟨11,84811714,84811772⟩,
⟨67,498144529,498144875⟩,
⟨123,914260110,914260746⟩,
⟨128,950450203,950450864⟩]
theorem checked13795 : checkPrefixCuts (2^48) 1812070401 9 Manual.Count131072.C013795.packed 128 cuts13795 = true := by
 decide +kernel
def pointBounds13795 : List (Nat × Nat × Nat) := [(1812081664,95167743034479,95168120317300),(1812139008,95168156367294,95168533650403),(1812196352,95168572482875,95168949766274)]
theorem point_links_checked13795 : (cuts13795.take 3).map (fun c => (1812070401-1+2*2^9*c.k,95167658222765+c.lower,95168035505528+c.upper)) = pointBounds13795 := by
 decide +kernel
def cuts13796 : List PrefixCut := [⟨51,372767624,372767886⟩,
⟨107,790876035,790876592⟩,
⟨128,949759959,949760626⟩]
theorem checked13796 : checkPrefixCuts (2^48) 1812201473 9 Manual.Count131072.C013796.packed 128 cuts13796 = true := by
 decide +kernel
def pointBounds13796 : List (Nat × Nat × Nat) := [(1812253696,95168981440592,95169358724278),(1812311040,95169399549003,95169776832984)]
theorem point_links_checked13796 : (cuts13796.take 2).map (fun c => (1812201473-1+2*2^9*c.k,95168608672968+c.lower,95168985956392+c.upper)) = pointBounds13796 := by
 decide +kernel
def cuts13797 : List PrefixCut := [⟨35,271325329,271325520⟩,
⟨91,682107769,682108242⟩,
⟨128,962426464,962427128⟩]
theorem checked13797 : checkPrefixCuts (2^48) 1812332545 9 Manual.Count131072.C013797.packed 128 cuts13797 = true := by
 decide +kernel
def pointBounds13797 : List (Nat × Nat × Nat) := [(1812368384,95169829758256,95170207042538),(1812425728,95170240540696,95170617825260)]
theorem point_links_checked13797 : (cuts13797.take 2).map (fun c => (1812332545-1+2*2^9*c.k,95169558432927+c.lower,95169935717018+c.upper)) = pointBounds13797 := by
 decide +kernel
def cuts13798 : List PrefixCut := [⟨19,144893748,144893849⟩,
⟨75,557824431,557824825⟩,
⟨128,958163798,958164472⟩]
theorem checked13798 : checkPrefixCuts (2^48) 1812463617 9 Manual.Count131072.C013798.packed 128 cuts13798 = true := by
 decide +kernel
def pointBounds13798 : List (Nat × Nat × Nat) := [(1812483072,95170665753139,95171043037995),(1812540416,95171078683822,95171455968971)]
theorem point_links_checked13798 : (cuts13798.take 2).map (fun c => (1812463617-1+2*2^9*c.k,95170520859391+c.lower,95170898144146+c.upper)) = pointBounds13798 := by
 decide +kernel
def cuts13799 : List PrefixCut := [⟨3,20963914,20963928⟩,
⟨59,441477360,441477669⟩,
⟨115,854989970,854990568⟩,
⟨128,953746607,953747275⟩]
theorem checked13799 : checkPrefixCuts (2^48) 1812594689 9 Manual.Count131072.C013799.packed 128 cuts13799 = true := by
 decide +kernel
def pointBounds13799 : List (Nat × Nat × Nat) := [(1812597760,95171499987103,95171877272546),(1812655104,95171920500549,95172297786287),(1812712448,95172334013159,95172711299186)]
theorem point_links_checked13799 : (cuts13799.take 3).map (fun c => (1812594689-1+2*2^9*c.k,95171479023189+c.lower,95171856308618+c.upper)) = pointBounds13799 := by
 decide +kernel
def cuts13800 : List PrefixCut := [⟨43,323438364,323438588⟩,
⟨99,745775218,745775739⟩,
⟨128,963304533,963305209⟩]
theorem checked13800 : checkPrefixCuts (2^48) 1812725761 9 Manual.Count131072.C013800.packed 128 cuts13800 = true := by
 decide +kernel
def pointBounds13800 : List (Nat × Nat × Nat) := [(1812769792,95172756208160,95173133494481),(1812827136,95173178545014,95173555831632)]
theorem point_links_checked13800 : (cuts13800.take 2).map (fun c => (1812725761-1+2*2^9*c.k,95172432769796+c.lower,95172810055893+c.upper)) = pointBounds13800 := by
 decide +kernel
def cuts13801 : List PrefixCut := [⟨27,203086265,203086406⟩,
⟨83,626017495,626017933⟩,
⟨128,958422016,958422692⟩]
theorem checked13801 : checkPrefixCuts (2^48) 1812856833 9 Manual.Count131072.C013801.packed 128 cuts13801 = true := by
 decide +kernel
def pointBounds13801 : List (Nat × Nat × Nat) := [(1812884480,95173599160594,95173976447508),(1812941824,95174022091824,95174399379035)]
theorem point_links_checked13801 : (cuts13801.take 2).map (fun c => (1812856833-1+2*2^9*c.k,95173396074329+c.lower,95173773361102+c.upper)) = pointBounds13801 := by
 decide +kernel
def cuts13802 : List PrefixCut := [⟨11,87408114,87408175⟩,
⟨67,501929053,501929402⟩,
⟨123,918455138,918455776⟩,
⟨128,955558379,955559045⟩]
theorem checked13802 : checkPrefixCuts (2^48) 1812987905 9 Manual.Count131072.C013802.packed 128 cuts13802 = true := by
 decide +kernel
def pointBounds13802 : List (Nat × Nat × Nat) := [(1812999168,95174441904459,95174819191969),(1813056512,95174856425398,95175233713196),(1813113856,95175272951483,95175650239570)]
theorem point_links_checked13802 : (cuts13802.take 3).map (fun c => (1812987905-1+2*2^9*c.k,95174354496345+c.lower,95174731783794+c.upper)) = pointBounds13802 := by
 decide +kernel
def cuts13803 : List PrefixCut := [⟨51,373665660,373665923⟩,
⟨107,786439599,786440146⟩,
⟨128,944932680,944933338⟩]
theorem checked13803 : checkPrefixCuts (2^48) 1813118977 9 Manual.Count131072.C013803.packed 128 cuts13803 = true := by
 decide +kernel
def pointBounds13803 : List (Nat × Nat × Nat) := [(1813171200,95175683720384,95176061008762),(1813228544,95176096494323,95176473782985)]
theorem point_links_checked13803 : (cuts13803.take 2).map (fun c => (1813118977-1+2*2^9*c.k,95175310054724+c.lower,95175687342839+c.upper)) = pointBounds13803 := by
 decide +kernel
def cuts13804 : List PrefixCut := [⟨35,257682993,257683173⟩,
⟨91,679744488,679744960⟩,
⟨128,957127346,957128017⟩]
theorem checked13804 : checkPrefixCuts (2^48) 1813250049 9 Manual.Count131072.C013804.packed 128 cuts13804 = true := by
 decide +kernel
def pointBounds13804 : List (Nat × Nat × Nat) := [(1813285888,95176512670397,95176889959350),(1813343232,95176934731892,95177312021137)]
theorem point_links_checked13804 : (cuts13804.take 2).map (fun c => (1813250049-1+2*2^9*c.k,95176254987404+c.lower,95176632276177+c.upper)) = pointBounds13804 := by
 decide +kernel
def cuts13805 : List PrefixCut := [⟨19,139853405,139853504⟩,
⟨75,557231659,557232053⟩,
⟨128,949918318,949918981⟩]
theorem checked13805 : checkPrefixCuts (2^48) 1813381121 9 Manual.Count131072.C013805.packed 128 cuts13805 = true := by
 decide +kernel
def pointBounds13805 : List (Nat × Nat × Nat) := [(1813400576,95177351968155,95177729257698),(1813457920,95177769346409,95178146636247)]
theorem point_links_checked13805 : (cuts13805.take 2).map (fun c => (1813381121-1+2*2^9*c.k,95177212114750+c.lower,95177589404194+c.upper)) = pointBounds13805 := by
 decide +kernel
def cuts13806 : List PrefixCut := [⟨3,26230436,26230453⟩,
⟨59,440478101,440478408⟩,
⟨115,854247190,854247789⟩,
⟨128,948453080,948453747⟩]
theorem checked13806 : checkPrefixCuts (2^48) 1813512193 9 Manual.Count131072.C013806.packed 128 cuts13806 = true := by
 decide +kernel
def pointBounds13806 : List (Nat × Nat × Nat) := [(1813515264,95178188263504,95178565553628),(1813572608,95178602511169,95178979801583),(1813629952,95179016280258,95179393570964)]
theorem point_links_checked13806 : (cuts13806.take 3).map (fun c => (1813512193-1+2*2^9*c.k,95178162033068+c.lower,95178539323175+c.upper)) = pointBounds13806 := by
 decide +kernel
def cuts13807 : List PrefixCut := [⟨43,319550022,319550248⟩,
⟨99,743070085,743070606⟩,
⟨128,954902553,954903223⟩]
theorem checked13807 : checkPrefixCuts (2^48) 1813643265 9 Manual.Count131072.C013807.packed 128 cuts13807 = true := by
 decide +kernel
def pointBounds13807 : List (Nat × Nat × Nat) := [(1813687296,95179430036170,95179807327170),(1813744640,95179853556233,95180230847528)]
theorem point_links_checked13807 : (cuts13807.take 2).map (fun c => (1813643265-1+2*2^9*c.k,95179110486148+c.lower,95179487776922+c.upper)) = pointBounds13807 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000118
