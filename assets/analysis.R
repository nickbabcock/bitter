library(scales)
library(tidyverse)
library(readr)

is_bitter <- Vectorize(function(fn) {
  switch(fn,
         "bitter-checked" = TRUE,
         "bitter-unchecked" = TRUE,
         FALSE)
})

get_line_type <- Vectorize(function(fn) {
  switch(fn,
         "bitter-checked" = "bitter",
         "bitter-unchecked" = "bitter",
         "other")
})

df <- read_csv("./benchmark-data.csv")

# `value`` is parameterized bits to read
BITS_PER_BYTE <- 8

df <- mutate(df,
             fn = `function`,
             bitter = is_bitter(fn),
             line = get_line_type(fn),
             throughput = value * iteration_count * 1000 * 10^9 / (sample_time_nanos * BITS_PER_BYTE)
)

pal <- hue_pal()(df %>% select(fn) %>% distinct() %>% count() %>% pull())
names(pal) <- df %>% select(fn) %>% distinct() %>% pull()

byte_rate <- function(l) {
  paste(scales::number_bytes(l, symbol = "MB", units = "si"), "/s")
}

ggplot(df, aes(value, throughput, color = fn)) +
  stat_summary(fun.y = mean, geom="point", size = 1.5) +
  stat_summary(aes(linetype = line), fun.y = mean, geom="line", size = 1.2) +
  scale_y_continuous(labels = byte_rate, limits = c(0, NA), breaks = pretty_breaks(10)) +
  scale_x_continuous(limit = c(1, NA), breaks = c(1, 4, 8, 12, 16, 20, 24, 28, 32)) +
  labs(title = "Comparison of throughput for Rust bit readers at varying lengths",
       caption = "solid lines are bitter functions",
       col = "Bit reader",
       y = "Throughput",
       x = "Read size (bits)") +
  guides(linetype = FALSE) +
  scale_colour_manual(values = pal)
ggsave('bench-bit-reads.png', width = 8, height = 5, dpi = 100)

reldf <- df %>%
  filter(value == 1 | value == 2 | value == 4 | value == 8 | value == 16 | value == 32) %>%
  mutate(throughput = throughput / 10^6) %>%
  group_by(group, fn, bitter, value) %>%
  summarize(throughput = mean(throughput)) %>%
  ungroup() %>%
  group_by(value) %>%
  mutate(relative = throughput / max(throughput)) %>%
  ungroup() %>%
  complete(group, fn, value, fill = list(bitter = FALSE))

ggplot(reldf, aes(fn, as.factor(value))) +
  geom_tile(aes(fill = relative), color = "white") +
  scale_x_discrete(position = "top") +
  scale_fill_gradient(name = "", low = "white", high = "steelblue", na.value = "#D8D8D8", labels = c("lowest", "highest (MB/s)"), breaks = c(0,1)) +
  xlab("Library") +
  ylab("Read size (bits)") +
  geom_text(size = 3.25, aes(label = ifelse(is.na(relative), "NA", format(round(throughput, 2), digits = 3)))) +
  theme(axis.text.x.top=element_text(angle=45, hjust=0, vjust=0)) +
  theme(plot.caption = element_text(hjust=0)) +
  ggtitle("Comparison of Mean Throughput (MB/s) of Rust bit readers", subtitle = "at varying bit-sized reads") +
  labs(caption = "Fastest libraries at each read size are shaded darker")
ggsave('bench-bit-table.png', width = 8, height = 5, dpi = 100)
