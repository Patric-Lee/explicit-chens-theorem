import PlattAssemblyKernel
import PlattCertificates.Count131072.C011856
import PlattCertificates.Count131072.C011857
import PlattCertificates.Count131072.C011858
import PlattCertificates.Count131072.C011859
import PlattCertificates.Count131072.C011860
import PlattCertificates.Count131072.C011861
import PlattCertificates.Count131072.C011862
import PlattCertificates.Count131072.C011863
import PlattCertificates.Count131072.C011864
import PlattCertificates.Count131072.C011865
import PlattCertificates.Count131072.C011866
import PlattCertificates.Count131072.C011867
import PlattCertificates.Count131072.C011868
import PlattCertificates.Count131072.C011869
import PlattCertificates.Count131072.C011870
import PlattCertificates.Count131072.C011871
import PlattCertificates.Count131072.C011872
import PlattCertificates.Count131072.C011873
import PlattCertificates.Count131072.C011874
import PlattCertificates.Count131072.C011875
import PlattCertificates.Count131072.C011876
import PlattCertificates.Count131072.C011877
import PlattCertificates.Count131072.C011878
import PlattCertificates.Count131072.C011879
import PlattCertificates.Count131072.C011880
import PlattCertificates.Count131072.C011881
import PlattCertificates.Count131072.C011882
import PlattCertificates.Count131072.C011883
import PlattCertificates.Count131072.C011884
import PlattCertificates.Count131072.C011885
import PlattCertificates.Count131072.C011886
import PlattCertificates.Count131072.C011887
namespace ChenEffective.PlattWindow.Assembly.Prefix.S2.B000058
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts11856 : List PrefixCut := [⟨41,364413208,364413490⟩,
⟨89,774885407,774886008⟩,
⟨128,1104590647,1104591504⟩]
theorem checked11856 : checkPrefixCuts (2^48) 1557921793 9 Manual.Count131072.C011856.packed 128 cuts11856 = true := by
 decide +kernel
def pointBounds11856 : List (Nat × Nat × Nat) := [(1557963776,93165651578204,93166027391399),(1558012928,93166062050403,93166437863917)]
theorem point_links_checked11856 : (cuts11856.take 2).map (fun c => (1557921793-1+2*2^9*c.k,93165287164996+c.lower,93165662977909+c.upper)) = pointBounds11856 := by
 decide +kernel
def cuts11857 : List PrefixCut := [⟨9,83825101,83825166⟩,
⟨57,501858841,501859227⟩,
⟨105,917530956,917531664⟩,
⟨128,1121297740,1121298607⟩]
theorem checked11857 : checkPrefixCuts (2^48) 1558052865 9 Manual.Count131072.C011857.packed 128 cuts11857 = true := by
 decide +kernel
def pointBounds11857 : List (Nat × Nat × Nat) := [(1558062080,93166475580744,93166851394579),(1558111232,93166893614484,93167269428640),(1558160384,93167309286599,93167685101077)]
theorem point_links_checked11857 : (cuts11857.take 3).map (fun c => (1558052865-1+2*2^9*c.k,93166391755643+c.lower,93166767569413+c.upper)) = pointBounds11857 := by
 decide +kernel
def cuts11858 : List PrefixCut := [⟨25,219298685,219298855⟩,
⟨73,637112315,637112812⟩,
⟨121,1057441458,1057442280⟩,
⟨128,1120300043,1120300911⟩]
theorem checked11858 : checkPrefixCuts (2^48) 1558183937 9 Manual.Count131072.C011858.packed 128 cuts11858 = true := by
 decide +kernel
def pointBounds11858 : List (Nat × Nat × Nat) := [(1558209536,93167732352068,93168108166875),(1558258688,93168150165698,93168525980832),(1558307840,93168570494841,93168946310300)]
theorem point_links_checked11858 : (cuts11858.take 3).map (fun c => (1558183937-1+2*2^9*c.k,93167513053383+c.lower,93167888868020+c.upper)) = pointBounds11858 := by
 decide +kernel
def cuts11859 : List PrefixCut := [⟨41,354206167,354206434⟩,
⟨89,783901003,783901596⟩,
⟨128,1123818087,1123818946⟩]
theorem checked11859 : checkPrefixCuts (2^48) 1558315009 9 Manual.Count131072.C011859.packed 128 cuts11859 = true := by
 decide +kernel
def pointBounds11859 : List (Nat × Nat × Nat) := [(1558356992,93168987559593,93169363375365),(1558406144,93169417254429,93169793070527)]
theorem point_links_checked11859 : (cuts11859.take 2).map (fun c => (1558315009-1+2*2^9*c.k,93168633353426+c.lower,93169009168931+c.upper)) = pointBounds11859 := by
 decide +kernel
def cuts11860 : List PrefixCut := [⟨9,78927436,78927498⟩,
⟨57,489089619,489089999⟩,
⟨105,894181951,894182649⟩,
⟨128,1091215156,1091216006⟩]
theorem checked11860 : checkPrefixCuts (2^48) 1558446081 9 Manual.Count131072.C011860.packed 128 cuts11860 = true := by
 decide +kernel
def pointBounds11860 : List (Nat × Nat × Nat) := [(1558455296,93169836098949,93170211915375),(1558504448,93170246261132,93170622077876),(1558553600,93170651353464,93171027170526)]
theorem point_links_checked11860 : (cuts11860.take 3).map (fun c => (1558446081-1+2*2^9*c.k,93169757171513+c.lower,93170132987877+c.upper)) = pointBounds11860 := by
 decide +kernel
def cuts11861 : List PrefixCut := [⟨25,215992632,215992796⟩,
⟨73,641827493,641827982⟩,
⟨121,1064759417,1064760231⟩,
⟨128,1127421563,1127422426⟩]
theorem checked11861 : checkPrefixCuts (2^48) 1558577153 9 Manual.Count131072.C011861.packed 128 cuts11861 = true := by
 decide +kernel
def pointBounds11861 : List (Nat × Nat × Nat) := [(1558602752,93171064379301,93171440196679),(1558651904,93171490214162,93171866031865),(1558701056,93171913146086,93172288964114)]
theorem point_links_checked11861 : (cuts11861.take 3).map (fun c => (1558577153-1+2*2^9*c.k,93170848386669+c.lower,93171224203883+c.upper)) = pointBounds11861 := by
 decide +kernel
def cuts11862 : List PrefixCut := [⟨41,361520653,361520932⟩,
⟨89,792551794,792552405⟩,
⟨128,1129855134,1129856005⟩]
theorem checked11862 : checkPrefixCuts (2^48) 1558708225 9 Manual.Count131072.C011862.packed 128 cuts11862 = true := by
 decide +kernel
def pointBounds11862 : List (Nat × Nat × Nat) := [(1558750208,93172337328885,93172713147241),(1558799360,93172768360026,93173144178714)]
theorem point_links_checked11862 : (cuts11862.take 2).map (fun c => (1558708225-1+2*2^9*c.k,93171975808232+c.lower,93172351626309+c.upper)) = pointBounds11862 := by
 decide +kernel
def cuts11863 : List PrefixCut := [⟨9,76921300,76921359⟩,
⟨57,499077695,499078080⟩,
⟨105,915803977,915804679⟩,
⟨128,1117120741,1117121598⟩]
theorem checked11863 : checkPrefixCuts (2^48) 1558839297 9 Manual.Count131072.C011863.packed 128 cuts11863 = true := by
 decide +kernel
def pointBounds11863 : List (Nat × Nat × Nat) := [(1558848512,93173182584666,93173558403673),(1558897664,93173604741061,93173980560394),(1558946816,93174021467343,93174397286993)]
theorem point_links_checked11863 : (cuts11863.take 3).map (fun c => (1558839297-1+2*2^9*c.k,93173105663366+c.lower,93173481482314+c.upper)) = pointBounds11863 := by
 decide +kernel
def cuts11864 : List PrefixCut := [⟨25,221535201,221535370⟩,
⟨73,647443097,647443592⟩,
⟨121,1070810015,1070810838⟩,
⟨128,1135261731,1135262603⟩]
theorem checked11864 : checkPrefixCuts (2^48) 1558970369 9 Manual.Count131072.C011864.packed 128 cuts11864 = true := by
 decide +kernel
def pointBounds11864 : List (Nat × Nat × Nat) := [(1558995968,93174444319308,93174820139282),(1559045120,93174870227204,93175246047504),(1559094272,93175293594122,93175669414750)]
theorem point_links_checked11864 : (cuts11864.take 3).map (fun c => (1558970369-1+2*2^9*c.k,93174222784107+c.lower,93174598603912+c.upper)) = pointBounds11864 := by
 decide +kernel
def cuts11865 : List PrefixCut := [⟨41,355652363,355652638⟩,
⟨89,776104199,776104797⟩,
⟨128,1124153897,1124154760⟩]
theorem checked11865 : checkPrefixCuts (2^48) 1559101441 9 Manual.Count131072.C011865.packed 128 cuts11865 = true := by
 decide +kernel
def pointBounds11865 : List (Nat × Nat × Nat) := [(1559143424,93175713698201,93176089519153),(1559192576,93176134150037,93176509971312)]
theorem point_links_checked11865 : (cuts11865.take 2).map (fun c => (1559101441-1+2*2^9*c.k,93175358045838+c.lower,93175733866515+c.upper)) = pointBounds11865 := by
 decide +kernel
def cuts11866 : List PrefixCut := [⟨9,76179813,76179874⟩,
⟨57,488120800,488121179⟩,
⟨105,910698930,910699634⟩,
⟨128,1115214074,1115214935⟩]
theorem checked11866 : checkPrefixCuts (2^48) 1559232513 9 Manual.Count131072.C011866.packed 128 cuts11866 = true := by
 decide +kernel
def pointBounds11866 : List (Nat × Nat × Nat) := [(1559241728,93176558379548,93176934201149),(1559290880,93176970320535,93177346142454),(1559340032,93177392898665,93177768720909)]
theorem point_links_checked11866 : (cuts11866.take 3).map (fun c => (1559232513-1+2*2^9*c.k,93176482199735+c.lower,93176858021275+c.upper)) = pointBounds11866 := by
 decide +kernel
def cuts11867 : List PrefixCut := [⟨25,222201375,222201545⟩,
⟨73,637352456,637352948⟩,
⟨121,1051948930,1051949736⟩,
⟨128,1110969646,1110970497⟩]
theorem checked11867 : checkPrefixCuts (2^48) 1559363585 9 Manual.Count131072.C011867.packed 128 cuts11867 = true := by
 decide +kernel
def pointBounds11867 : List (Nat × Nat × Nat) := [(1559389184,93177819615184,93178195437755),(1559438336,93178234766265,93178610589158),(1559487488,93178649362739,93179025185946)]
theorem point_links_checked11867 : (cuts11867.take 3).map (fun c => (1559363585-1+2*2^9*c.k,93177597413809+c.lower,93177973236210+c.upper)) = pointBounds11867 := by
 decide +kernel
def cuts11868 : List PrefixCut := [⟨41,359713877,359714154⟩,
⟨89,778976803,778977403⟩,
⟨128,1114485875,1114486736⟩]
theorem checked11868 : checkPrefixCuts (2^48) 1559494657 9 Manual.Count131072.C011868.packed 128 cuts11868 = true := by
 decide +kernel
def pointBounds11868 : List (Nat × Nat × Nat) := [(1559536640,93179068097332,93179443920861),(1559585792,93179487360258,93179863184110)]
theorem point_links_checked11868 : (cuts11868.take 2).map (fun c => (1559494657-1+2*2^9*c.k,93178708383455+c.lower,93179084206707+c.upper)) = pointBounds11868 := by
 decide +kernel
def cuts11869 : List PrefixCut := [⟨9,77784890,77784948⟩,
⟨57,501172278,501172659⟩,
⟨105,925629088,925629801⟩,
⟨128,1120889074,1120889939⟩]
theorem checked11869 : checkPrefixCuts (2^48) 1559625729 9 Manual.Count131072.C011869.packed 128 cuts11869 = true := by
 decide +kernel
def pointBounds11869 : List (Nat × Nat × Nat) := [(1559634944,93179900654220,93180276478391),(1559684096,93180324041608,93180699866102),(1559733248,93180748498418,93181124323244)]
theorem point_links_checked11869 : (cuts11869.take 3).map (fun c => (1559625729-1+2*2^9*c.k,93179822869330+c.lower,93180198693443+c.upper)) = pointBounds11869 := by
 decide +kernel
def cuts11870 : List PrefixCut := [⟨25,215107454,215107620⟩,
⟨73,639717864,639718359⟩,
⟨121,1054751184,1054751999⟩,
⟨128,1119350850,1119351714⟩]
theorem checked11870 : checkPrefixCuts (2^48) 1559756801 9 Manual.Count131072.C011870.packed 128 cuts11870 = true := by
 decide +kernel
def pointBounds11870 : List (Nat × Nat × Nat) := [(1559782400,93181158865858,93181534691002),(1559831552,93181583476268,93181959301741),(1559880704,93181998509588,93182374335381)]
theorem point_links_checked11870 : (cuts11870.take 3).map (fun c => (1559756801-1+2*2^9*c.k,93180943758404+c.lower,93181319583382+c.upper)) = pointBounds11870 := by
 decide +kernel
def cuts11871 : List PrefixCut := [⟨41,358720990,358721264⟩,
⟨89,780043413,780044014⟩,
⟨128,1112761346,1112762203⟩]
theorem checked11871 : checkPrefixCuts (2^48) 1559887873 9 Manual.Count131072.C011871.packed 128 cuts11871 = true := by
 decide +kernel
def pointBounds11871 : List (Nat × Nat × Nat) := [(1559929856,93182421830244,93182797656360),(1559979008,93182843152667,93183218979110)]
theorem point_links_checked11871 : (cuts11871.take 2).map (fun c => (1559887873-1+2*2^9*c.k,93182063109254+c.lower,93182438935096+c.upper)) = pointBounds11871 := by
 decide +kernel
def cuts11872 : List PrefixCut := [⟨9,82817315,82817378⟩,
⟨57,491663808,491664188⟩,
⟨105,913126776,913127481⟩,
⟨128,1113028428,1113029286⟩]
theorem checked11872 : checkPrefixCuts (2^48) 1560018945 9 Manual.Count131072.C011872.packed 128 cuts11872 = true := by
 decide +kernel
def pointBounds11872 : List (Nat × Nat × Nat) := [(1560028160,93183258687915,93183634514677),(1560077312,93183667534408,93184043361487),(1560126464,93184088997376,93184464824780)]
theorem point_links_checked11872 : (cuts11872.take 3).map (fun c => (1560018945-1+2*2^9*c.k,93183175870600+c.lower,93183551697299+c.upper)) = pointBounds11872 := by
 decide +kernel
def cuts11873 : List PrefixCut := [⟨25,218661533,218661701⟩,
⟨73,642443418,642443911⟩,
⟨121,1071443575,1071444396⟩,
⟨128,1127006933,1127007800⟩]
theorem checked11873 : checkPrefixCuts (2^48) 1560150017 9 Manual.Count131072.C011873.packed 128 cuts11873 = true := by
 decide +kernel
def pointBounds11873 : List (Nat × Nat × Nat) := [(1560175616,93184507560561,93184883388286),(1560224768,93184931342446,93185307170496),(1560273920,93185360342603,93185736170981)]
theorem point_links_checked11873 : (cuts11873.take 3).map (fun c => (1560150017-1+2*2^9*c.k,93184288899028+c.lower,93184664726585+c.upper)) = pointBounds11873 := by
 decide +kernel
def cuts11874 : List PrefixCut := [⟨41,348889100,348889368⟩,
⟨89,765956378,765956971⟩,
⟨128,1112841120,1112841985⟩]
theorem checked11874 : checkPrefixCuts (2^48) 1560281089 9 Manual.Count131072.C011874.packed 128 cuts11874 = true := by
 decide +kernel
def pointBounds11874 : List (Nat × Nat × Nat) := [(1560323072,93185764795061,93186140623753),(1560372224,93186181862339,93186557691356)]
theorem point_links_checked11874 : (cuts11874.take 2).map (fun c => (1560281089-1+2*2^9*c.k,93185415905961+c.lower,93185791734385+c.upper)) = pointBounds11874 := by
 decide +kernel
def cuts11875 : List PrefixCut := [⟨9,78286840,78286898⟩,
⟨57,484144184,484144555⟩,
⟨105,899007539,899008232⟩,
⟨128,1098137288,1098138135⟩]
theorem checked11875 : checkPrefixCuts (2^48) 1560412161 9 Manual.Count131072.C011875.packed 128 cuts11875 = true := by
 decide +kernel
def pointBounds11875 : List (Nat × Nat × Nat) := [(1560421376,93186607033921,93186982863268),(1560470528,93187012891265,93187388720925),(1560519680,93187427754620,93187803584602)]
theorem point_links_checked11875 : (cuts11875.take 3).map (fun c => (1560412161-1+2*2^9*c.k,93186528747081+c.lower,93186904576370+c.upper)) = pointBounds11875 := by
 decide +kernel
def cuts11876 : List PrefixCut := [⟨25,217343848,217344015⟩,
⟨73,639936806,639937299⟩,
⟨121,1062336021,1062336836⟩,
⟨128,1122213905,1122214768⟩]
theorem checked11876 : checkPrefixCuts (2^48) 1560543233 9 Manual.Count131072.C011876.packed 128 cuts11876 = true := by
 decide +kernel
def pointBounds11876 : List (Nat × Nat × Nat) := [(1560568832,93187844228217,93188220058520),(1560617984,93188266821175,93188642651804),(1560667136,93188689220390,93189065051341)]
theorem point_links_checked11876 : (cuts11876.take 3).map (fun c => (1560543233-1+2*2^9*c.k,93187626884369+c.lower,93188002714505+c.upper)) = pointBounds11876 := by
 decide +kernel
def cuts11877 : List PrefixCut := [⟨41,351145788,351146062⟩,
⟨89,766304585,766305179⟩,
⟨128,1098313832,1098314688⟩]
theorem checked11877 : checkPrefixCuts (2^48) 1560674305 9 Manual.Count131072.C011877.packed 128 cuts11877 = true := by
 decide +kernel
def pointBounds11877 : List (Nat × Nat × Nat) := [(1560716288,93189100244062,93189476075335),(1560765440,93189515402859,93189891234452)]
theorem point_links_checked11877 : (cuts11877.take 2).map (fun c => (1560674305-1+2*2^9*c.k,93188749098274+c.lower,93189124929273+c.upper)) = pointBounds11877 := by
 decide +kernel
def cuts11878 : List PrefixCut := [⟨9,79890163,79890225⟩,
⟨57,496645779,496646164⟩,
⟨105,919339094,919339805⟩,
⟨128,1122566171,1122567038⟩]
theorem checked11878 : checkPrefixCuts (2^48) 1560805377 9 Manual.Count131072.C011878.packed 128 cuts11878 = true := by
 decide +kernel
def pointBounds11878 : List (Nat × Nat × Nat) := [(1560814592,93189927302269,93190303134186),(1560863744,93190344057885,93190719890125),(1560912896,93190766751200,93191142583766)]
theorem point_links_checked11878 : (cuts11878.take 3).map (fun c => (1560805377-1+2*2^9*c.k,93189847412106+c.lower,93190223243961+c.upper)) = pointBounds11878 := by
 decide +kernel
def cuts11879 : List PrefixCut := [⟨25,216207188,216207352⟩,
⟨73,636890342,636890827⟩,
⟨121,1045840073,1045840878⟩,
⟨128,1107145345,1107146199⟩]
theorem checked11879 : checkPrefixCuts (2^48) 1560936449 9 Manual.Count131072.C011879.packed 128 cuts11879 = true := by
 decide +kernel
def pointBounds11879 : List (Nat × Nat × Nat) := [(1560962048,93191186185465,93191562018351),(1561011200,93191606868619,93191982701826),(1561060352,93192015818350,93192391651877)]
theorem point_links_checked11879 : (cuts11879.take 3).map (fun c => (1560936449-1+2*2^9*c.k,93190969978277+c.lower,93191345810999+c.upper)) = pointBounds11879 := by
 decide +kernel
def cuts11880 : List PrefixCut := [⟨41,361515171,361515449⟩,
⟨89,772963253,772963846⟩,
⟨128,1122918496,1122919358⟩]
theorem checked11880 : checkPrefixCuts (2^48) 1561067521 9 Manual.Count131072.C011880.packed 128 cuts11880 = true := by
 decide +kernel
def pointBounds11880 : List (Nat × Nat × Nat) := [(1561109504,93192438638793,93192814472647),(1561158656,93192850086875,93193225921044)]
theorem point_links_checked11880 : (cuts11880.take 2).map (fun c => (1561067521-1+2*2^9*c.k,93192077123622+c.lower,93192452957198+c.upper)) = pointBounds11880 := by
 decide +kernel
def cuts11881 : List PrefixCut := [⟨9,79148870,79148929⟩,
⟨57,490030205,490030578⟩,
⟨105,913518471,913519167⟩,
⟨128,1108762029,1108762877⟩]
theorem checked11881 : checkPrefixCuts (2^48) 1561198593 9 Manual.Count131072.C011881.packed 128 cuts11881 = true := by
 decide +kernel
def pointBounds11881 : List (Nat × Nat × Nat) := [(1561207808,93193279190988,93193655025485),(1561256960,93193690072323,93194065907134),(1561306112,93194113560589,93194489395723)]
theorem point_links_checked11881 : (cuts11881.take 3).map (fun c => (1561198593-1+2*2^9*c.k,93193200042118+c.lower,93193575876556+c.upper)) = pointBounds11881 := by
 decide +kernel
def cuts11882 : List PrefixCut := [⟨25,212907663,212907827⟩,
⟨73,633304606,633305095⟩,
⟨121,1053327849,1053328666⟩,
⟨128,1114437427,1114438292⟩]
theorem checked11882 : checkPrefixCuts (2^48) 1561329665 9 Manual.Count131072.C011882.packed 128 cuts11882 = true := by
 decide +kernel
def pointBounds11882 : List (Nat × Nat × Nat) := [(1561355264,93194521711810,93194897547260),(1561404416,93194942108753,93195317944528),(1561453568,93195362131996,93195737968099)]
theorem point_links_checked11882 : (cuts11882.take 3).map (fun c => (1561329665-1+2*2^9*c.k,93194308804147+c.lower,93194684639433+c.upper)) = pointBounds11882 := by
 decide +kernel
def cuts11883 : List PrefixCut := [⟨41,346282160,346282425⟩,
⟨89,763394800,763395388⟩,
⟨128,1112721248,1112722102⟩]
theorem checked11883 : checkPrefixCuts (2^48) 1561460737 9 Manual.Count131072.C011883.packed 128 cuts11883 = true := by
 decide +kernel
def pointBounds11883 : List (Nat × Nat × Nat) := [(1561502720,93195769523734,93196145360150),(1561551872,93196186636374,93196562473113)]
theorem point_links_checked11883 : (cuts11883.take 2).map (fun c => (1561460737-1+2*2^9*c.k,93195423241574+c.lower,93195799077725+c.upper)) = pointBounds11883 := by
 decide +kernel
def cuts11884 : List PrefixCut := [⟨9,79669682,79669743⟩,
⟨57,487563572,487563949⟩,
⟨105,908602168,908602875⟩,
⟨128,1109744328,1109745191⟩]
theorem checked11884 : checkPrefixCuts (2^48) 1561591809 9 Manual.Count131072.C011884.packed 128 cuts11884 = true := by
 decide +kernel
def pointBounds11884 : List (Nat × Nat × Nat) := [(1561601024,93196615632504,93196991469570),(1561650176,93197023526394,93197399363776),(1561699328,93197444564990,93197820402702)]
theorem point_links_checked11884 : (cuts11884.take 3).map (fun c => (1561591809-1+2*2^9*c.k,93196535962822+c.lower,93196911799827+c.upper)) = pointBounds11884 := by
 decide +kernel
def cuts11885 : List PrefixCut := [⟨25,217900588,217900755⟩,
⟨73,634947632,634948122⟩,
⟨121,1046935388,1046936192⟩,
⟨128,1107849357,1107850209⟩]
theorem checked11885 : checkPrefixCuts (2^48) 1561722881 9 Manual.Count131072.C011885.packed 128 cuts11885 = true := by
 decide +kernel
def pointBounds11885 : List (Nat × Nat × Nat) := [(1561748480,93197863607738,93198239445773),(1561797632,93198280654782,93198656493140),(1561846784,93198692642538,93199068481210)]
theorem point_links_checked11885 : (cuts11885.take 3).map (fun c => (1561722881-1+2*2^9*c.k,93197645707150+c.lower,93198021545018+c.upper)) = pointBounds11885 := by
 decide +kernel
def cuts11886 : List PrefixCut := [⟨41,354665036,354665309⟩,
⟨89,767708090,767708681⟩,
⟨128,1102349911,1102350763⟩]
theorem checked11886 : checkPrefixCuts (2^48) 1561853953 9 Manual.Count131072.C011886.packed 128 cuts11886 = true := by
 decide +kernel
def pointBounds11886 : List (Nat × Nat × Nat) := [(1561895936,93199108221543,93199484060536),(1561945088,93199521264597,93199897103908)]
theorem point_links_checked11886 : (cuts11886.take 2).map (fun c => (1561853953-1+2*2^9*c.k,93198753556507+c.lower,93199129395227+c.upper)) = pointBounds11886 := by
 decide +kernel
def cuts11887 : List PrefixCut := [⟨9,85055713,85055777⟩,
⟨57,495550025,495550407⟩,
⟨105,913779748,913780452⟩,
⟨128,1118294894,1118295759⟩]
theorem checked11887 : checkPrefixCuts (2^48) 1561985025 9 Manual.Count131072.C011887.packed 128 cuts11887 = true := by
 decide +kernel
def pointBounds11887 : List (Nat × Nat × Nat) := [(1561994240,93199940962131,93200316801767),(1562043392,93200351456443,93200727296397),(1562092544,93200769686166,93201145526442)]
theorem point_links_checked11887 : (cuts11887.take 3).map (fun c => (1561985025-1+2*2^9*c.k,93199855906418+c.lower,93200231745990+c.upper)) = pointBounds11887 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S2.B000058
