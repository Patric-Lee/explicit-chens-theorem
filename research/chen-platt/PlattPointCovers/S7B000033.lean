import PlattPointSubsetKernel
import PlattPointPackets.S2B000160
import PlattPointPackets.S2B000161
import PlattPointPackets.S2B000162
import PlattPointPackets.S2B000163
import PlattPointPackets.S2B000164
import PlattGlobalGrid.S7B000033
namespace ChenEffective.PlattWindow.PointCovers.S7B000033
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := ((((ChenEffective.PlattWindow.PointPackets.S2B000160.points ++ ChenEffective.PlattWindow.PointPackets.S2B000161.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000162.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000163.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000164.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S7B000033.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S7B000033.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S7B000033
