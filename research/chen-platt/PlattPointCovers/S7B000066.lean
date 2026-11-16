import PlattPointSubsetKernel
import PlattPointPackets.S2B000304
import PlattPointPackets.S2B000305
import PlattPointPackets.S2B000306
import PlattPointPackets.S2B000307
import PlattPointPackets.S2B000308
import PlattPointPackets.S2B000309
import PlattGlobalGrid.S7B000066
namespace ChenEffective.PlattWindow.PointCovers.S7B000066
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def sourcePoints : List PrimePoint := (((((ChenEffective.PlattWindow.PointPackets.S2B000304.points ++ ChenEffective.PlattWindow.PointPackets.S2B000305.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000306.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000307.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000308.points) ++ ChenEffective.PlattWindow.PointPackets.S2B000309.points)
theorem checked : checkPointCoverAux 1000000 sourcePoints ChenEffective.PlattWindow.GlobalGrid.S7B000066.points=true := by decide +kernel
theorem covered : PointSubset ChenEffective.PlattWindow.GlobalGrid.S7B000066.points sourcePoints := .checked checked
#print axioms covered
end ChenEffective.PlattWindow.PointCovers.S7B000066
