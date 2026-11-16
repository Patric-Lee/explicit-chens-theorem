import PlattAssemblyKernel
import PlattCertificates.Count131072.C028000
import PlattCertificates.Count131072.C028001
import PlattCertificates.Count131072.C028002
import PlattCertificates.Count131072.C028003
import PlattCertificates.Count131072.C028004
import PlattCertificates.Count131072.C028005
import PlattCertificates.Count131072.C028006
import PlattCertificates.Count131072.C028007
import PlattCertificates.Count131072.C028008
import PlattCertificates.Count131072.C028009
import PlattCertificates.Count131072.C028010
import PlattCertificates.Count131072.C028011
import PlattCertificates.Count131072.C028012
import PlattCertificates.Count131072.C028013
import PlattCertificates.Count131072.C028014
import PlattCertificates.Count131072.C028015
import PlattCertificates.Count131072.C028016
import PlattCertificates.Count131072.C028017
import PlattCertificates.Count131072.C028018
import PlattCertificates.Count131072.C028019
import PlattCertificates.Count131072.C028020
import PlattCertificates.Count131072.C028021
import PlattCertificates.Count131072.C028022
import PlattCertificates.Count131072.C028023
import PlattCertificates.Count131072.C028024
import PlattCertificates.Count131072.C028025
import PlattCertificates.Count131072.C028026
import PlattCertificates.Count131072.C028027
import PlattCertificates.Count131072.C028028
import PlattCertificates.Count131072.C028029
import PlattCertificates.Count131072.C028030
import PlattCertificates.Count131072.C028031
namespace ChenEffective.PlattWindow.Assembly.Prefix.S3.B000250
set_option maxRecDepth 100000
set_option maxHeartbeats 0
def cuts28000 : List PrefixCut := [⟨13,46887523,46887550⟩,
⟨126,449868023,449868279⟩,
⟨128,457375904,457376163⟩]
theorem checked28000 : checkPrefixCuts (2^48) 3673948161 9 Manual.Count131072.C028000.packed 128 cuts28000 = true := by
 decide +kernel
def pointBounds28000 : List (Nat × Nat × Nat) := [(3673961472,104348604898016,104348987726540),(3674077184,104349007878516,104349390707269)]
theorem point_links_checked28000 : (cuts28000.take 2).map (fun c => (3673948161-1+2*2^9*c.k,104348558010493+c.lower,104348940838990+c.upper)) = pointBounds28000 := by
 decide +kernel
def cuts28001 : List PrefixCut := [⟨111,391935796,391936016⟩,
⟨128,452686293,452686549⟩]
theorem checked28001 : checkPrefixCuts (2^48) 3674079233 9 Manual.Count131072.C028001.packed 128 cuts28001 = true := by
 decide +kernel
def pointBounds28001 : List (Nat × Nat × Nat) := [(3674192896,104349407322193,104349790151169)]
theorem point_links_checked28001 : (cuts28001.take 1).map (fun c => (3674079233-1+2*2^9*c.k,104349015386397+c.lower,104349398215153+c.upper)) = pointBounds28001 := by
 decide +kernel
def cuts28002 : List PrefixCut := [⟨96,341898142,341898333⟩,
⟨128,453895945,453896198⟩]
theorem checked28002 : checkPrefixCuts (2^48) 3674210305 9 Manual.Count131072.C028002.packed 128 cuts28002 = true := by
 decide +kernel
def pointBounds28002 : List (Nat × Nat × Nat) := [(3674308608,104349809970832,104350192800035)]
theorem point_links_checked28002 : (cuts28002.take 1).map (fun c => (3674210305-1+2*2^9*c.k,104349468072690+c.lower,104349850901702+c.upper)) = pointBounds28002 := by
 decide +kernel
def cuts28003 : List PrefixCut := [⟨81,284739602,284739762⟩,
⟨128,452730634,452730886⟩]
theorem checked28003 : checkPrefixCuts (2^48) 3674341377 9 Manual.Count131072.C028003.packed 128 cuts28003 = true := by
 decide +kernel
def pointBounds28003 : List (Nat × Nat × Nat) := [(3674424320,104350206708237,104350589537662)]
theorem point_links_checked28003 : (cuts28003.take 1).map (fun c => (3674341377-1+2*2^9*c.k,104349921968635+c.lower,104350304797900+c.upper)) = pointBounds28003 := by
 decide +kernel
def cuts28004 : List PrefixCut := [⟨66,238615544,238615676⟩,
⟨128,460068266,460068525⟩]
theorem checked28004 : checkPrefixCuts (2^48) 3674472449 9 Manual.Count131072.C028004.packed 128 cuts28004 = true := by
 decide +kernel
def pointBounds28004 : List (Nat × Nat × Nat) := [(3674540032,104350613314813,104350996144462)]
theorem point_links_checked28004 : (cuts28004.take 1).map (fun c => (3674472449-1+2*2^9*c.k,104350374699269+c.lower,104350757528786+c.upper)) = pointBounds28004 := by
 decide +kernel
def cuts28005 : List PrefixCut := [⟨51,181540883,181540986⟩,
⟨128,459821982,459822239⟩]
theorem checked28005 : checkPrefixCuts (2^48) 3674603521 9 Manual.Count131072.C028005.packed 128 cuts28005 = true := by
 decide +kernel
def pointBounds28005 : List (Nat × Nat × Nat) := [(3674655744,104351016308418,104351399138297)]
theorem point_links_checked28005 : (cuts28005.take 1).map (fun c => (3674603521-1+2*2^9*c.k,104350834767535+c.lower,104351217597311+c.upper)) = pointBounds28005 := by
 decide +kernel
def cuts28006 : List PrefixCut := [⟨36,131363780,131363853⟩,
⟨128,465550345,465550601⟩]
theorem checked28006 : checkPrefixCuts (2^48) 3674734593 9 Manual.Count131072.C028006.packed 128 cuts28006 = true := by
 decide +kernel
def pointBounds28006 : List (Nat × Nat × Nat) := [(3674771456,104351425953297,104351808783403)]
theorem point_links_checked28006 : (cuts28006.take 1).map (fun c => (3674734593-1+2*2^9*c.k,104351294589517+c.lower,104351677419550+c.upper)) = pointBounds28006 := by
 decide +kernel
def cuts28007 : List PrefixCut := [⟨21,74679519,74679559⟩,
⟨128,459482846,459483101⟩]
theorem checked28007 : checkPrefixCuts (2^48) 3674865665 9 Manual.Count131072.C028007.packed 128 cuts28007 = true := by
 decide +kernel
def pointBounds28007 : List (Nat × Nat × Nat) := [(3674887168,104351834819381,104352217649710)]
theorem point_links_checked28007 : (cuts28007.take 1).map (fun c => (3674865665-1+2*2^9*c.k,104351760139862+c.lower,104352142970151+c.upper)) = pointBounds28007 := by
 decide +kernel
def cuts28008 : List PrefixCut := [⟨6,20986156,20986170⟩,
⟨119,426226702,426226942⟩,
⟨128,460385505,460385764⟩]
theorem checked28008 : checkPrefixCuts (2^48) 3674996737 9 Manual.Count131072.C028008.packed 128 cuts28008 = true := by
 decide +kernel
def pointBounds28008 : List (Nat × Nat × Nat) := [(3675002880,104352240608864,104352623439422),(3675118592,104352645849410,104353028680194)]
theorem point_links_checked28008 : (cuts28008.take 2).map (fun c => (3674996737-1+2*2^9*c.k,104352219622708+c.lower,104352602453252+c.upper)) = pointBounds28008 := by
 decide +kernel
def cuts28009 : List PrefixCut := [⟨104,373596470,373596677⟩,
⟨128,459220366,459220621⟩]
theorem checked28009 : checkPrefixCuts (2^48) 3675127809 9 Manual.Count131072.C028009.packed 128 cuts28009 = true := by
 decide +kernel
def pointBounds28009 : List (Nat × Nat × Nat) := [(3675234304,104353053604683,104353436435693)]
theorem point_links_checked28009 : (cuts28009.take 1).map (fun c => (3675127809-1+2*2^9*c.k,104352680008213+c.lower,104353062839016+c.upper)) = pointBounds28009 := by
 decide +kernel
def cuts28010 : List PrefixCut := [⟨89,313540885,313541058⟩,
⟨128,451315678,451315923⟩]
theorem checked28010 : checkPrefixCuts (2^48) 3675258881 9 Manual.Count131072.C028010.packed 128 cuts28010 = true := by
 decide +kernel
def pointBounds28010 : List (Nat × Nat × Nat) := [(3675350016,104353452769464,104353835600695)]
theorem point_links_checked28010 : (cuts28010.take 1).map (fun c => (3675258881-1+2*2^9*c.k,104353139228579+c.lower,104353522059637+c.upper)) = pointBounds28010 := by
 decide +kernel
def cuts28011 : List PrefixCut := [⟨74,264900217,264900366⟩,
⟨128,459110979,459111237⟩]
theorem checked28011 : checkPrefixCuts (2^48) 3675389953 9 Manual.Count131072.C028011.packed 128 cuts28011 = true := by
 decide +kernel
def pointBounds28011 : List (Nat × Nat × Nat) := [(3675465728,104353855444474,104354238275926)]
theorem point_links_checked28011 : (cuts28011.take 1).map (fun c => (3675389953-1+2*2^9*c.k,104353590544257+c.lower,104353973375560+c.upper)) = pointBounds28011 := by
 decide +kernel
def cuts28012 : List PrefixCut := [⟨59,211055366,211055482⟩,
⟨128,453657505,453657759⟩]
theorem checked28012 : checkPrefixCuts (2^48) 3675521025 9 Manual.Count131072.C028012.packed 128 cuts28012 = true := by
 decide +kernel
def pointBounds28012 : List (Nat × Nat × Nat) := [(3675581440,104354260710602,104354643542279)]
theorem point_links_checked28012 : (cuts28012.take 1).map (fun c => (3675521025-1+2*2^9*c.k,104354049655236+c.lower,104354432486797+c.upper)) = pointBounds28012 := by
 decide +kernel
def cuts28013 : List PrefixCut := [⟨44,154227610,154227699⟩,
⟨128,453105281,453105538⟩]
theorem checked28013 : checkPrefixCuts (2^48) 3675652097 9 Manual.Count131072.C028013.packed 128 cuts28013 = true := by
 decide +kernel
def pointBounds28013 : List (Nat × Nat × Nat) := [(3675697152,104354657540351,104355040372255)]
theorem point_links_checked28013 : (cuts28013.take 1).map (fun c => (3675652097-1+2*2^9*c.k,104354503312741+c.lower,104354886144556+c.upper)) = pointBounds28013 := by
 decide +kernel
def cuts28014 : List PrefixCut := [⟨29,102917039,102917097⟩,
⟨128,454467431,454467686⟩]
theorem checked28014 : checkPrefixCuts (2^48) 3675783169 9 Manual.Count131072.C028014.packed 128 cuts28014 = true := by
 decide +kernel
def pointBounds28014 : List (Nat × Nat × Nat) := [(3675812864,104355059335061,104355442167191)]
theorem point_links_checked28014 : (cuts28014.take 1).map (fun c => (3675783169-1+2*2^9*c.k,104354956418022+c.lower,104355339250094+c.upper)) = pointBounds28014 := by
 decide +kernel
def cuts28015 : List PrefixCut := [⟨14,50844218,50844245⟩,
⟨127,445722161,445722409⟩,
⟨128,449244383,449244633⟩]
theorem checked28015 : checkPrefixCuts (2^48) 3675914241 9 Manual.Count131072.C028015.packed 128 cuts28015 = true := by
 decide +kernel
def pointBounds28015 : List (Nat × Nat × Nat) := [(3675928576,104355461729671,104355844562025),(3676044288,104355856607614,104356239440189)]
theorem point_links_checked28015 : (cuts28015.take 2).map (fun c => (3675914241-1+2*2^9*c.k,104355410885453+c.lower,104355793717780+c.upper)) = pointBounds28015 := by
 decide +kernel
def cuts28016 : List PrefixCut := [⟨112,398157924,398158148⟩,
⟨128,454741281,454741536⟩]
theorem checked28016 : checkPrefixCuts (2^48) 3676045313 9 Manual.Count131072.C028016.packed 128 cuts28016 = true := by
 decide +kernel
def pointBounds28016 : List (Nat × Nat × Nat) := [(3676160000,104356258287760,104356641120561)]
theorem point_links_checked28016 : (cuts28016.take 1).map (fun c => (3676045313-1+2*2^9*c.k,104355860129836+c.lower,104356242962413+c.upper)) = pointBounds28016 := by
 decide +kernel
def cuts28017 : List PrefixCut := [⟨97,349754752,349754947⟩,
⟨128,457787818,457788075⟩]
theorem checked28017 : checkPrefixCuts (2^48) 3676176385 9 Manual.Count131072.C028017.packed 128 cuts28017 = true := by
 decide +kernel
def pointBounds28017 : List (Nat × Nat × Nat) := [(3676275712,104356664625869,104357047458896)]
theorem point_links_checked28017 : (cuts28017.take 1).map (fun c => (3676176385-1+2*2^9*c.k,104356314871117+c.lower,104356697703949+c.upper)) = pointBounds28017 := by
 decide +kernel
def cuts28018 : List PrefixCut := [⟨82,286271657,286271819⟩,
⟨128,453713464,453713722⟩]
theorem checked28018 : checkPrefixCuts (2^48) 3676307457 9 Manual.Count131072.C028018.packed 128 cuts28018 = true := by
 decide +kernel
def pointBounds28018 : List (Nat × Nat × Nat) := [(3676391424,104357058930592,104357441763843)]
theorem point_links_checked28018 : (cuts28018.take 1).map (fun c => (3676307457-1+2*2^9*c.k,104356772658935+c.lower,104357155492024+c.upper)) = pointBounds28018 := by
 decide +kernel
def cuts28019 : List PrefixCut := [⟨67,241244090,241244223⟩,
⟨128,458520694,458520944⟩]
theorem checked28019 : checkPrefixCuts (2^48) 3676438529 9 Manual.Count131072.C028019.packed 128 cuts28019 = true := by
 decide +kernel
def pointBounds28019 : List (Nat × Nat × Nat) := [(3676507136,104357467616489,104357850449969)]
theorem point_links_checked28019 : (cuts28019.take 1).map (fun c => (3676438529-1+2*2^9*c.k,104357226372399+c.lower,104357609205746+c.upper)) = pointBounds28019 := by
 decide +kernel
def cuts28020 : List PrefixCut := [⟨52,184582686,184582791⟩,
⟨128,455748254,455748509⟩]
theorem checked28020 : checkPrefixCuts (2^48) 3676569601 9 Manual.Count131072.C028020.packed 128 cuts28020 = true := by
 decide +kernel
def pointBounds28020 : List (Nat × Nat × Nat) := [(3676622848,104357869475779,104358252309481)]
theorem point_links_checked28020 : (cuts28020.take 1).map (fun c => (3676569601-1+2*2^9*c.k,104357684893093+c.lower,104358067726690+c.upper)) = pointBounds28020 := by
 decide +kernel
def cuts28021 : List PrefixCut := [⟨37,130604495,130604570⟩,
⟨128,452975988,452976245⟩]
theorem checked28021 : checkPrefixCuts (2^48) 3676700673 9 Manual.Count131072.C028021.packed 128 cuts28021 = true := by
 decide +kernel
def pointBounds28021 : List (Nat × Nat × Nat) := [(3676738560,104358271245842,104358654079769)]
theorem point_links_checked28021 : (cuts28021.take 1).map (fun c => (3676700673-1+2*2^9*c.k,104358140641347+c.lower,104358523475199+c.upper)) = pointBounds28021 := by
 decide +kernel
def cuts28022 : List PrefixCut := [⟨22,78237593,78237636⟩,
⟨128,453266084,453266336⟩]
theorem checked28022 : checkPrefixCuts (2^48) 3676831745 9 Manual.Count131072.C028022.packed 128 cuts28022 = true := by
 decide +kernel
def pointBounds28022 : List (Nat × Nat × Nat) := [(3676854272,104358671854928,104359054689080)]
theorem point_links_checked28022 : (cuts28022.take 1).map (fun c => (3676831745-1+2*2^9*c.k,104358593617335+c.lower,104358976451444+c.upper)) = pointBounds28022 := by
 decide +kernel
def cuts28023 : List PrefixCut := [⟨7,26563143,26563157⟩,
⟨120,428754572,428754813⟩,
⟨128,456465050,456465306⟩]
theorem checked28023 : checkPrefixCuts (2^48) 3676962817 9 Manual.Count131072.C028023.packed 128 cuts28023 = true := by
 decide +kernel
def pointBounds28023 : List (Nat × Nat × Nat) := [(3676969984,104359073446562,104359456280937),(3677085696,104359475637991,104359858472593)]
theorem point_links_checked28023 : (cuts28023.take 2).map (fun c => (3676962817-1+2*2^9*c.k,104359046883419+c.lower,104359429717780+c.upper)) = pointBounds28023 := by
 decide +kernel
def cuts28024 : List PrefixCut := [⟨105,374850989,374851198⟩,
⟨128,456372173,456372428⟩]
theorem checked28024 : checkPrefixCuts (2^48) 3677093889 9 Manual.Count131072.C028024.packed 128 cuts28024 = true := by
 decide +kernel
def pointBounds28024 : List (Nat × Nat × Nat) := [(3677201408,104359878199458,104360261034284)]
theorem point_links_checked28024 : (cuts28024.take 1).map (fun c => (3677093889-1+2*2^9*c.k,104359503348469+c.lower,104359886183086+c.upper)) = pointBounds28024 := by
 decide +kernel
def cuts28025 : List PrefixCut := [⟨90,316205324,316205500⟩,
⟨128,453753350,453753602⟩]
theorem checked28025 : checkPrefixCuts (2^48) 3677224961 9 Manual.Count131072.C028025.packed 128 cuts28025 = true := by
 decide +kernel
def pointBounds28025 : List (Nat × Nat × Nat) := [(3677317120,104360275925966,104360658761014)]
theorem point_links_checked28025 : (cuts28025.take 1).map (fun c => (3677224961-1+2*2^9*c.k,104359959720642+c.lower,104360342555514+c.upper)) = pointBounds28025 := by
 decide +kernel
def cuts28026 : List PrefixCut := [⟨75,265447456,265447605⟩,
⟨128,453660745,453661001⟩]
theorem checked28026 : checkPrefixCuts (2^48) 3677356033 9 Manual.Count131072.C028026.packed 128 cuts28026 = true := by
 decide +kernel
def pointBounds28026 : List (Nat × Nat × Nat) := [(3677432832,104360678921448,104361061756721)]
theorem point_links_checked28026 : (cuts28026.take 1).map (fun c => (3677356033-1+2*2^9*c.k,104360413473992+c.lower,104360796309116+c.upper)) = pointBounds28026 := by
 decide +kernel
def cuts28027 : List PrefixCut := [⟨60,215611406,215611525⟩,
⟨128,459614573,459614827⟩]
theorem checked28027 : checkPrefixCuts (2^48) 3677487105 9 Manual.Count131072.C028027.packed 128 cuts28027 = true := by
 decide +kernel
def pointBounds28027 : List (Nat × Nat × Nat) := [(3677548544,104361082746143,104361465581642)]
theorem point_links_checked28027 : (cuts28027.take 1).map (fun c => (3677487105-1+2*2^9*c.k,104360867134737+c.lower,104361249970117+c.upper)) = pointBounds28027 := by
 decide +kernel
def cuts28028 : List PrefixCut := [⟨45,160191531,160191621⟩,
⟨128,460057373,460057626⟩]
theorem checked28028 : checkPrefixCuts (2^48) 3677618177 9 Manual.Count131072.C028028.packed 128 cuts28028 = true := by
 decide +kernel
def pointBounds28028 : List (Nat × Nat × Nat) := [(3677664256,104361486940841,104361869776565)]
theorem point_links_checked28028 : (cuts28028.take 1).map (fun c => (3677618177-1+2*2^9*c.k,104361326749310+c.lower,104361709584944+c.upper)) = pointBounds28028 := by
 decide +kernel
def cuts28029 : List PrefixCut := [⟨30,107071393,107071453⟩,
⟨128,461112421,461112673⟩]
theorem checked28029 : checkPrefixCuts (2^48) 3677749249 9 Manual.Count131072.C028029.packed 128 cuts28029 = true := by
 decide +kernel
def pointBounds28029 : List (Nat × Nat × Nat) := [(3677779968,104361893878076,104362276714023)]
theorem point_links_checked28029 : (cuts28029.take 1).map (fun c => (3677749249-1+2*2^9*c.k,104361786806683+c.lower,104362169642570+c.upper)) = pointBounds28029 := by
 decide +kernel
def cuts28030 : List PrefixCut := [⟨15,56174244,56174272⟩,
⟨128,459948142,459948395⟩]
theorem checked28030 : checkPrefixCuts (2^48) 3677880321 9 Manual.Count131072.C028030.packed 128 cuts28030 = true := by
 decide +kernel
def pointBounds28030 : List (Nat × Nat × Nat) := [(3677895680,104362304093348,104362686929515),(3678011392,104362707867246,104363090703638)]
theorem point_links_checked28030 : (cuts28030.take 2).map (fun c => (3677880321-1+2*2^9*c.k,104362247919104+c.lower,104362630755243+c.upper)) = pointBounds28030 := by
 decide +kernel
def cuts28031 : List PrefixCut := [⟨113,404756079,404756303⟩,
⟨128,457023697,457023951⟩]
theorem checked28031 : checkPrefixCuts (2^48) 3678011393 9 Manual.Count131072.C028031.packed 128 cuts28031 = true := by
 decide +kernel
def pointBounds28031 : List (Nat × Nat × Nat) := [(3678127104,104363112623325,104363495459941)]
theorem point_links_checked28031 : (cuts28031.take 1).map (fun c => (3678011393-1+2*2^9*c.k,104362707867246+c.lower,104363090703638+c.upper)) = pointBounds28031 := by
 decide +kernel
end ChenEffective.PlattWindow.Assembly.Prefix.S3.B000250
