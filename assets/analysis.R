library(scales)
library(tidyverse)
library(readr)
library(ggnewscale)

is_bitter <- Vectorize(function(fn) {
  switch(fn,
         "bitter-auto" = TRUE,
         "bitter-manual" = TRUE,
         "bitter-unchecked" = TRUE,
         FALSE)
})

get_line_type <- Vectorize(function(fn) {
  switch(fn,
         "bitter-auto" = "bitter",
         "bitter-manual" = "bitter",
         "bitter-unchecked" = "bitter",
         "other")
})

df <- read_csv("./bitter-benchmark-data.csv")

df <- mutate(df,
             fn = `function`,
             bitter = is_bitter(fn),
             line = get_line_type(fn),
             latency = (iteration_count * 1000) / sample_measured_value,
)

functionNames <- df %>% select(fn) %>% distinct() %>% pull() %>% sort(decreasing = TRUE)
pal <- brewer.pal(length(functionNames), "Set1")
names(pal) <- functionNames

dfBitter <- df %>% filter(bitter == TRUE)
dfOther <- df %>% filter(bitter == FALSE)

ggplot(mapping = aes(value, latency)) +
  stat_summary(data = df, mapping=aes(value, latency, color = fn), fun = mean, geom="point", size = 1.5) +
  scale_color_manual("Points", values=pal, guide=FALSE) +
  ggnewscale::new_scale_color() +
  stat_summary(data = dfOther, mapping=aes(linetype = line, color = fn), fun = mean, geom="line", size = 1.2) +
  scale_color_manual("Other Crates", values=pal, guide=guide_legend(order = 2)) +
  scale_linetype(guide = FALSE) +
  ggnewscale::new_scale_color() +
  stat_summary(data = dfBitter, mapping=aes(linetype = line, color = fn), fun = mean, geom="line", size = 1.2) +
  scale_color_manual("Bitter", values=pal, guide=guide_legend(order = 1)) +
  scale_y_continuous(breaks = pretty_breaks(10)) +
  scale_x_continuous(breaks = c(seq(1, 64, 4), 64)) +
  labs(title = "Rust Bit Readers Performance Comparison",
       subtitle = "Performance measured in reads per nanosecond (higher is better)",
       caption = "Bitter implementations marked with solid lines",
       col = "Bit reader",
       y = "Reads per ns",
       x = "Read size (bits)")
ggsave('bench-bit-reads.png', width = 9, height = 5, dpi = 100)
