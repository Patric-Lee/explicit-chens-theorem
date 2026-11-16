import PlattPointSubsetKernel
import PlattPointPackets.S2B000086
import PlattPointPackets.S2B000087
import PlattPointPackets.S2B000088
import PlattPointPackets.S2B000089
import PlattGlobalGrid.S7B000012
namespace ChenEffective.PlattWindow.PointCovers.S7B000012
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((ChenEffective.PlattWindow.PointPackets.S2B000086.points ++ ChenEffective.PlattWindow.PointPackets.S2B000087.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000088.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000089.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S7B000012.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S7B000012.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S7B000012
